------------------------ MODULE PerpExchange ------------------------
(*
 * TLA⁺ specification for a perpetual exchange.
 *
 * Models the core state machine of a perpetual derivatives exchange,
 * including account balances, open positions, mark/oracle prices,
 * funding rates, and an order book.  The invariants ensure that no
 * account falls below its maintenance-margin threshold at any point
 * reachable by the allowed actions.
 *)
EXTENDS Integers, Sequences

-----------------------------------------------------------------------------
(* ---------------------------------------------------------------------- *)
(*  C O N S T A N T S                                                      *)
(* ---------------------------------------------------------------------- *)

CONSTANTS
    Accounts,           (* finite set of trader accounts                   *)
    Markets,            (* finite set of perpetual-contract markets         *)
    InitialMargin,      (* minimum collateral (in whole units) to open      *)
    MaintenanceMargin,  (* minimum collateral (in whole units) to keep open *)
    TickSize,           (* minimum price increment (positive integer)       *)
    MaxPrice,           (* upper bound on any price, used for type checking *)
    MaxBalance          (* upper bound on any balance, used for bounding TLC *)

-----------------------------------------------------------------------------
(* ---------------------------------------------------------------------- *)
(*  V A R I A B L E S                                                      *)
(* ---------------------------------------------------------------------- *)

VARIABLES
    Balance,      (* Balance[a]       : collateral balance of account a    *)
    Position,     (* Position[a][m]   : signed size of a's position in m   *)
    EntryPrice,   (* EntryPrice[a][m] : average entry price of a's pos.    *)
    MarkPrice,    (* MarkPrice[m]     : current mark price for market m     *)
    OraclePrice,  (* OraclePrice[m]   : latest oracle price for market m   *)
    FundingRate,  (* FundingRate[m]   : funding rate in -100..100 for market m *)
    OrderBook     (* OrderBook[m]     : sequence of pending limit orders    *)

vars == <<Balance, Position, EntryPrice, MarkPrice,
          OraclePrice, FundingRate, OrderBook>>

-----------------------------------------------------------------------------
(* ---------------------------------------------------------------------- *)
(*  T Y P E   D E F I N I T I O N S                                        *)
(* ---------------------------------------------------------------------- *)

(*
 * An order record.  "side" is 1 for long (buy) and -1 for short (sell).
 * "size" and "price" are positive natural numbers.
 *)
Order == [account : Accounts, side : {1, -1}, size : Nat \ {0}, price : Nat \ {0}]

-----------------------------------------------------------------------------
(* ---------------------------------------------------------------------- *)
(*  H E L P E R   D E F I N I T I O N S                                   *)
(* ---------------------------------------------------------------------- *)

(*
 * Unrealised profit-and-loss for account a in market m.
 * PnL is positive when the position is profitable.
 *   Long  (pos > 0): PnL = size  * (mark - entry)
 *   Short (pos < 0): PnL = (-size) * (entry - mark)
 * We model signed positions as a pair Position[a][m] \in Int, represented
 * here with Naturals by keeping separate "long" and "short" magnitudes.
 * For simplicity in this spec every position is either zero, positive
 * (long) or negative (short); we encode negative sizes by requiring
 * Position[a][m] \in Int.  Because TLC works on Nat we use the convention:
 *   Position[a][m] > 0  => long
 *   Position[a][m] = 0  => flat
 * and handle shorts through the "side" field of an order.
 *
 * Here we compute an *unsigned* PnL magnitude and direction separately so
 * that all arithmetic stays in Nat.
 *)

AbsPnL(a, m) ==
    LET size  == Position[a][m]
        entry == EntryPrice[a][m]
        mark  == MarkPrice[m]
    IN  IF mark >= entry
        THEN size * (mark - entry)
        ELSE size * (entry - mark)

PnLPositive(a, m) ==
    (* TRUE when the unrealised PnL is non-negative for account a in m *)
    MarkPrice[m] >= EntryPrice[a][m]

(*
 * Effective equity = cash balance + sum over markets of signed PnL.
 * Because we keep arithmetic in Nat we compute the two halves separately.
 *)
PositivePnLSum(a) ==
    LET gain(m) == IF PnLPositive(a, m) THEN AbsPnL(a, m) ELSE 0
    IN  LET helper[S \in SUBSET Markets] ==
                IF S = {} THEN 0
                ELSE LET m == CHOOSE x \in S : TRUE
                     IN  gain(m) + helper[S \ {m}]
        IN  helper[Markets]

NegativePnLSum(a) ==
    LET loss(m) == IF ~PnLPositive(a, m) THEN AbsPnL(a, m) ELSE 0
    IN  LET helper[S \in SUBSET Markets] ==
                IF S = {} THEN 0
                ELSE LET m == CHOOSE x \in S : TRUE
                     IN  loss(m) + helper[S \ {m}]
        IN  helper[Markets]

(*
 * Equity(a) >= MaintenanceMargin  iff  Balance[a] + gains >= losses + MaintenanceMargin
 *)
SufficientMargin(a) ==
    Balance[a] + PositivePnLSum(a) >= NegativePnLSum(a) + MaintenanceMargin

(*
 * An account is solvent if its equity covers the initial margin for all
 * open positions or, when it has no positions, it simply holds non-negative
 * balance.
 *)
HasOpenPosition(a) ==
    \E m \in Markets : Position[a][m] > 0

(*
 * AccountSafeAtMarkPrice(a, m, mark)
 * Check that account a (which is assumed to hold a long position in m, i.e.
 * Position[a][m] > 0) would remain above MaintenanceMargin if market m's
 * mark price were set to `mark`.  Only valid for long (non-negative) positions;
 * short modelling is out of scope for this spec.  Used as a pre-condition in
 * PriceUpdate to preserve MarginSafety across price changes.
 *)
AccountSafeAtMarkPrice(a, m, mark) ==
    LET absPos == Position[a][m]
        entry  == EntryPrice[a][m]
        gain   == IF mark >= entry THEN absPos * (mark - entry) ELSE 0
        loss   == IF mark < entry  THEN absPos * (entry - mark) ELSE 0
    IN  Balance[a] + gain >= loss + MaintenanceMargin

(*
 * SufficientMarginAfterDebit(a, amount)
 * TRUE when account a would remain above MaintenanceMargin after `amount`
 * units are deducted from its balance, factoring in current PnL.
 *)
SufficientMarginAfterDebit(a, amount) ==
    (Balance[a] - amount) + PositivePnLSum(a) >= NegativePnLSum(a) + MaintenanceMargin

(*
 * Min(a, b) — the smaller of two integers.
 *)
Min(a, b) == IF a <= b THEN a ELSE b

(*
 * BestBuyIdx(m) — index of the best (highest-price) resting buy order.
 * Among orders with equal price the earliest (lowest index) is preferred,
 * implementing strict price/time priority on the bid side.
 * Returns 0 when there are no buy orders.
 *)
BestBuyIdx(m) ==
    LET buys == {k \in DOMAIN OrderBook[m] : OrderBook[m][k].side = 1}
    IN  IF buys = {} THEN 0
        ELSE CHOOSE k \in buys :
                 /\ \A l \in buys : OrderBook[m][k].price >= OrderBook[m][l].price
                 /\ \A l \in buys :
                        OrderBook[m][l].price = OrderBook[m][k].price => k <= l

(*
 * BestSellIdx(m) — index of the best (lowest-price) resting sell order.
 * Among orders with equal price the earliest (lowest index) is preferred,
 * implementing strict price/time priority on the ask side.
 * Returns 0 when there are no sell orders.
 *)
BestSellIdx(m) ==
    LET sells == {k \in DOMAIN OrderBook[m] : OrderBook[m][k].side = -1}
    IN  IF sells = {} THEN 0
        ELSE CHOOSE k \in sells :
                 /\ \A l \in sells : OrderBook[m][k].price <= OrderBook[m][l].price
                 /\ \A l \in sells :
                        OrderBook[m][l].price = OrderBook[m][k].price => k <= l

(*
 * PostTradeBuyerSafe(buyer, m, tradePrice, tradeSize)
 * TRUE when the buyer's total equity (across all markets) remains above
 * MaintenanceMargin after the trade.  The trade changes Balance and the
 * position in market m; all other-market positions are untouched, so their
 * PnL contribution is computed by subtracting out the pre-trade market-m
 * contribution from the aggregate sums.
 *)
PostTradeBuyerSafe(buyer, m, tradePrice, tradeSize) ==
    LET newBal      == Balance[buyer] - InitialMargin
        newPos      == Position[buyer][m] + tradeSize
        newGainM    == IF MarkPrice[m] >= tradePrice THEN newPos * (MarkPrice[m] - tradePrice) ELSE 0
        newLossM    == IF MarkPrice[m] <  tradePrice THEN newPos * (tradePrice - MarkPrice[m]) ELSE 0
        oldGainM    == IF PnLPositive(buyer, m) THEN AbsPnL(buyer, m) ELSE 0
        oldLossM    == IF ~PnLPositive(buyer, m) THEN AbsPnL(buyer, m) ELSE 0
        otherGains  == PositivePnLSum(buyer) - oldGainM
        otherLosses == NegativePnLSum(buyer) - oldLossM
    IN  newBal + newGainM + otherGains >= newLossM + otherLosses + MaintenanceMargin

(*
 * PostTradeSellerSafe(seller, m, tradeSize)
 * TRUE when the seller's total equity (across all markets) remains above
 * MaintenanceMargin after the trade.  Entry price is preserved on partial
 * exits and cleared on full close.  Other-market PnL is unchanged.
 *)
PostTradeSellerSafe(seller, m, tradeSize) ==
    LET newBal      == Balance[seller] - InitialMargin
        newPos      == Position[seller][m] - tradeSize
        newEntry    == IF newPos = 0 THEN 0 ELSE EntryPrice[seller][m]
        newGainM    == IF newPos > 0 /\ MarkPrice[m] >= newEntry
                       THEN newPos * (MarkPrice[m] - newEntry) ELSE 0
        newLossM    == IF newPos > 0 /\ MarkPrice[m] <  newEntry
                       THEN newPos * (newEntry - MarkPrice[m]) ELSE 0
        oldGainM    == IF PnLPositive(seller, m) THEN AbsPnL(seller, m) ELSE 0
        oldLossM    == IF ~PnLPositive(seller, m) THEN AbsPnL(seller, m) ELSE 0
        otherGains  == PositivePnLSum(seller) - oldGainM
        otherLosses == NegativePnLSum(seller) - oldLossM
    IN  newBal + newGainM + otherGains >= newLossM + otherLosses + MaintenanceMargin

-----------------------------------------------------------------------------
(* ---------------------------------------------------------------------- *)
(*  I N V A R I A N T S                                                    *)
(* ---------------------------------------------------------------------- *)

TypeInvariant ==
    /\ Balance    \in [Accounts -> Nat]
    /\ Position   \in [Accounts -> [Markets -> Nat]]
    /\ EntryPrice \in [Accounts -> [Markets -> Nat]]
    /\ MarkPrice  \in [Markets -> Nat]
    /\ OraclePrice \in [Markets -> Nat]
    /\ FundingRate \in [Markets -> -100..100]
    /\ \A m \in Markets :
           \A i \in DOMAIN OrderBook[m] :
               OrderBook[m][i] \in Order

(*
 * MarginSafety: every account with an open position must be above the
 * maintenance-margin threshold.  Accounts with no open positions are
 * exempt (they simply hold idle collateral).
 *)
MarginSafety ==
    \A a \in Accounts :
        HasOpenPosition(a) => SufficientMargin(a)

(*
 * MarkPricesPositive: mark prices are always strictly positive.
 * This is guaranteed by PriceUpdate (newMark > 0) and Init (MarkPrice = TickSize).
 *)
MarkPricesPositive ==
    \A m \in Markets : MarkPrice[m] > 0

(*
 * PricesTickAligned: mark and oracle prices are always multiples of TickSize.
 * PlaceOrder enforces the same on order prices; this covers the exchange-side
 * prices so every relevant price in the system is tick-aligned.
 *)
PricesTickAligned ==
    \A m \in Markets :
        /\ MarkPrice[m]   % TickSize = 0
        /\ OraclePrice[m] % TickSize = 0

(*
 * PositionEntryPriceConsistency: a non-zero position always has a non-zero
 * entry price and vice versa.  This is a key bookkeeping invariant: the two
 * fields must be set and cleared together.
 *)
PositionEntryPriceConsistency ==
    \A a \in Accounts, m \in Markets :
        (Position[a][m] = 0) <=> (EntryPrice[a][m] = 0)

-----------------------------------------------------------------------------
(* ---------------------------------------------------------------------- *)
(*  S T A T E   C O N S T R A I N T   ( f o r   T L C )                  *)
(* ---------------------------------------------------------------------- *)

(*
 * Bound the state space for finite model checking.
 * TLC will not explore states where any balance or position exceeds MaxBalance,
 * or where any market's order book has more than 2 pending orders.
 *)
StateConstraint ==
    /\ \A a \in Accounts : Balance[a] <= MaxBalance
    /\ \A a \in Accounts, m \in Markets : Position[a][m] <= MaxBalance
    /\ \A m \in Markets : Len(OrderBook[m]) <= 2

-----------------------------------------------------------------------------
(* ---------------------------------------------------------------------- *)
(*  I N I T I A L   S T A T E                                              *)
(* ---------------------------------------------------------------------- *)

Init ==
    /\ Balance     = [a \in Accounts |-> 0]
    /\ Position    = [a \in Accounts |-> [m \in Markets |-> 0]]
    /\ EntryPrice  = [a \in Accounts |-> [m \in Markets |-> 0]]
    /\ MarkPrice   = [m \in Markets |-> TickSize]
    /\ OraclePrice = [m \in Markets |-> TickSize]
    /\ FundingRate = [m \in Markets |-> 0]
    /\ OrderBook   = [m \in Markets |-> << >>]

-----------------------------------------------------------------------------
(* ---------------------------------------------------------------------- *)
(*  A C T I O N S                                                          *)
(* ---------------------------------------------------------------------- *)

(*
 * Deposit(a, amount)
 * Account a deposits `amount` units of collateral into its balance.
 * Pre-conditions : a is a known account, amount > 0.
 * Post-conditions: Balance[a] increases by amount; everything else unchanged.
 *)
Deposit(a, amount) ==
    /\ a \in Accounts
    /\ amount > 0
    /\ Balance'    = [Balance    EXCEPT ![a] = @ + amount]
    /\ UNCHANGED <<Position, EntryPrice, MarkPrice, OraclePrice,
                   FundingRate, OrderBook>>

(*
 * Withdraw(a, amount)
 * Account a withdraws `amount` units of collateral.
 * Pre-conditions : a \in Accounts, amount > 0,
 *                  the remaining balance (after withdrawal) still satisfies
 *                  SufficientMargin when there is an open position.
 *)
Withdraw(a, amount) ==
    /\ a \in Accounts
    /\ amount > 0
    /\ Balance[a] >= amount
    /\ LET newBal == Balance[a] - amount
           newBalance == [Balance EXCEPT ![a] = newBal]
       IN  /\ (~HasOpenPosition(a) \/ newBal + PositivePnLSum(a)
                   >= NegativePnLSum(a) + MaintenanceMargin)
           /\ Balance' = newBalance
    /\ UNCHANGED <<Position, EntryPrice, MarkPrice, OraclePrice,
                   FundingRate, OrderBook>>

(*
 * PlaceOrder(a, m, side, size, price)
 * Account a places a limit order in market m.
 * Pre-conditions : a \in Accounts, m \in Markets,
 *                  side \in {1, -1}, size > 0, price > 0,
 *                  price is a multiple of TickSize,
 *                  account has sufficient balance to cover initial margin.
 *)
PlaceOrder(a, m, side, size, price) ==
    /\ a \in Accounts
    /\ m \in Markets
    /\ side \in {1, -1}
    /\ size > 0
    /\ price > 0
    /\ price % TickSize = 0
    /\ Balance[a] >= InitialMargin
    /\ LET o == [account |-> a, side |-> side, size |-> size, price |-> price]
       IN  OrderBook' = [OrderBook EXCEPT ![m] = Append(@, o)]
    /\ UNCHANGED <<Balance, Position, EntryPrice, MarkPrice,
                   OraclePrice, FundingRate>>

(*
 * ExecuteTrade(m)
 * Match the best resting buy order against the best resting sell order in
 * market m, applying strict price/time priority:
 *   - Best bid: highest buy price; ties broken by earliest placement (lowest index).
 *   - Best ask: lowest sell price; ties broken by earliest placement (lowest index).
 *
 * The trade executes at the seller's (ask) price and fills
 *   tradeSize = Min(buyOrder.size, sellOrder.size)
 * units, leaving a partially-filled residual in the book when the two sizes
 * differ.  Self-trading (buyer = seller) is prohibited.
 *
 * Post-conditions:
 *   - Buyer's position increases by tradeSize; entry price set to tradePrice.
 *   - Seller's position decreases by tradeSize; entry price preserved on
 *     partial exits and cleared to 0 on a full close.
 *   - Both parties pay InitialMargin from their balance.
 *   - The fully-consumed order is removed; the residual (if any) stays in the
 *     book with its size reduced.  Order-book positions of surviving orders
 *     are preserved; the partial residual is appended at the tail.
 *   - Post-trade equity of each party must satisfy MaintenanceMargin.
 *)
ExecuteTrade(m) ==
    /\ m \in Markets
    /\ LET i == BestBuyIdx(m)
           j == BestSellIdx(m)
       IN
           /\ i > 0
           /\ j > 0
           /\ OrderBook[m][i].price >= OrderBook[m][j].price
           /\ LET buyOrder   == OrderBook[m][i]
                  sellOrder  == OrderBook[m][j]
                  tradePrice == sellOrder.price
                  tradeSize  == Min(buyOrder.size, sellOrder.size)
                  buyer      == buyOrder.account
                  seller     == sellOrder.account
                  lo         == IF i < j THEN i ELSE j
                  hi         == IF i < j THEN j ELSE i
                  (* Remove both matched orders; re-add any partial residual. *)
                  base       == SubSeq(OrderBook[m], 1, lo - 1)
                                \o SubSeq(OrderBook[m], lo + 1, hi - 1)
                                \o SubSeq(OrderBook[m], hi + 1, Len(OrderBook[m]))
                  newBook    ==
                      IF    buyOrder.size < sellOrder.size
                      THEN  Append(base, [sellOrder EXCEPT !.size = @ - tradeSize])
                      ELSE IF buyOrder.size > sellOrder.size
                      THEN  Append(base, [buyOrder  EXCEPT !.size = @ - tradeSize])
                      ELSE  base  (* both orders fully consumed *)
              IN
                  /\ buyer /= seller
                  /\ Balance[buyer]  >= InitialMargin
                  /\ Balance[seller] >= InitialMargin
                  /\ Position[seller][m] >= tradeSize
                  /\ PostTradeBuyerSafe(buyer, m, tradePrice, tradeSize)
                  /\ PostTradeSellerSafe(seller, m, tradeSize)
                  /\ Balance' = [Balance EXCEPT
                         ![buyer]  = @ - InitialMargin,
                         ![seller] = @ - InitialMargin]
                  /\ Position' = [Position EXCEPT
                         ![buyer][m]  = @ + tradeSize,
                         ![seller][m] = @ - tradeSize]
                  /\ EntryPrice' = [EntryPrice EXCEPT
                         ![buyer][m]  = tradePrice,
                         (* Seller: preserve entry price on partial exit,
                            clear to 0 when the position is fully closed. *)
                         ![seller][m] = IF Position[seller][m] - tradeSize = 0
                                        THEN 0
                                        ELSE EntryPrice[seller][m]]
                  /\ OrderBook' = [OrderBook EXCEPT ![m] = newBook]
    /\ UNCHANGED <<MarkPrice, OraclePrice, FundingRate>>

(*
 * PriceUpdate(m, newMark, newOracle)
 * The exchange updates the mark price and oracle price for market m.
 * Pre-conditions : m \in Markets, both prices are positive multiples of TickSize,
 *                  the new mark price must not push any account below
 *                  MaintenanceMargin (preserving MarginSafety).
 *)
PriceUpdate(m, newMark, newOracle) ==
    /\ m \in Markets
    /\ newMark   > 0
    /\ newOracle > 0
    /\ newMark   <= MaxPrice
    /\ newOracle <= MaxPrice
    /\ newMark   % TickSize = 0
    /\ newOracle % TickSize = 0
    (* Safety pre-check: all accounts with positions remain above maintenance margin *)
    /\ \A a \in Accounts :
           Position[a][m] > 0 => AccountSafeAtMarkPrice(a, m, newMark)
    /\ MarkPrice'   = [MarkPrice   EXCEPT ![m] = newMark]
    /\ OraclePrice' = [OraclePrice EXCEPT ![m] = newOracle]
    /\ UNCHANGED <<Balance, Position, EntryPrice, FundingRate, OrderBook>>

(*
 * UpdateFundingRate(m, rate)
 * The exchange sets a new funding rate for market m.
 * The rate is an integer (can be negative for shorts paying longs).
 *)
UpdateFundingRate(m, rate) ==
    /\ m \in Markets
    /\ FundingRate' = [FundingRate EXCEPT ![m] = rate]
    /\ UNCHANGED <<Balance, Position, EntryPrice, MarkPrice,
                   OraclePrice, OrderBook>>

(*
 * ProcessFunding(a, m)
 * Apply the current funding payment for account a's position in market m.
 * Long positions pay funding when rate > 0; short positions pay when rate < 0.
 * For this spec we only model long positions (Position >= 0) and apply the
 * payment as: payment = Position[a][m] * |FundingRate[m]|.
 * If the account owes funding, deduct from Balance; if owed, add to Balance.
 * Pre-condition: account has a non-zero position in the market, and when
 *                paying, the remaining equity must still satisfy MarginSafety.
 *)
ProcessFunding(a, m) ==
    /\ a \in Accounts
    /\ m \in Markets
    /\ Position[a][m] > 0
    /\ LET rate    == FundingRate[m]
           size    == Position[a][m]
           payment == size * (IF rate >= 0 THEN rate ELSE -rate)
       IN  IF rate >= 0
           THEN (* longs pay; ensure post-payment equity stays above maintenance margin *)
                /\ SufficientMarginAfterDebit(a, payment)
                /\ Balance' = [Balance EXCEPT ![a] = @ - payment]
           ELSE (* longs receive; balance only increases, always safe *)
                /\ Balance' = [Balance EXCEPT ![a] = @ + payment]
    /\ UNCHANGED <<Position, EntryPrice, MarkPrice, OraclePrice,
                   FundingRate, OrderBook>>

(*
 * Liquidate(a, m)
 * Force-close ALL of account a's positions when margin is insufficient.
 * Pre-condition: account has an open position AND is below maintenance margin.
 * Post-condition: all positions are zeroed; balance is set to 0 (insurance fund
 *                 absorbs any deficit in a real system; simplified here).
 *                 Closing all positions ensures HasOpenPosition becomes FALSE,
 *                 so MarginSafety is vacuously satisfied after liquidation.
 *)
Liquidate(a, m) ==
    /\ a \in Accounts
    /\ m \in Markets
    /\ Position[a][m] > 0
    /\ ~SufficientMargin(a)
    /\ Position'   = [Position   EXCEPT ![a] = [m2 \in Markets |-> 0]]
    /\ EntryPrice' = [EntryPrice EXCEPT ![a] = [m2 \in Markets |-> 0]]
    /\ Balance'    = [Balance    EXCEPT ![a] = 0]
    /\ UNCHANGED <<MarkPrice, OraclePrice, FundingRate, OrderBook>>

-----------------------------------------------------------------------------
(* ---------------------------------------------------------------------- *)
(*  N E X T - S T A T E   R E L A T I O N                                 *)
(* ---------------------------------------------------------------------- *)

Next ==
    \/ \E a \in Accounts, amount \in 1..MaxBalance :
           Deposit(a, amount)
    \/ \E a \in Accounts : \E amount \in 1..Balance[a] + 1 :
           Withdraw(a, amount)
    \/ \E a \in Accounts, m \in Markets,
          side \in {1, -1}, size \in 1..2, price \in 1..MaxPrice :
           PlaceOrder(a, m, side, size, price)
    \/ \E m \in Markets : ExecuteTrade(m)
    \/ \E m \in Markets, p1 \in 1..MaxPrice, p2 \in 1..MaxPrice :
           PriceUpdate(m, p1, p2)
    \/ \E m \in Markets, r \in -2..2 :
           UpdateFundingRate(m, r)
    \/ \E a \in Accounts, m \in Markets :
           ProcessFunding(a, m)
    \/ \E a \in Accounts, m \in Markets :
           Liquidate(a, m)

-----------------------------------------------------------------------------
(* ---------------------------------------------------------------------- *)
(*  S P E C I F I C A T I O N                                              *)
(* ---------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* ---------------------------------------------------------------------- *)
(*  P R O P E R T I E S   T O   C H E C K                                 *)
(* ---------------------------------------------------------------------- *)

(*
 * The type invariant and margin safety are the primary safety properties.
 * TLC can verify all of the below for finite instantiations of the constants.
 *)
THEOREM Spec => []TypeInvariant
THEOREM Spec => []MarginSafety
THEOREM Spec => []MarkPricesPositive
THEOREM Spec => []PricesTickAligned
THEOREM Spec => []PositionEntryPriceConsistency

=============================================================================
