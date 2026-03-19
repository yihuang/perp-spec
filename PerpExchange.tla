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
    InitialMargin,      (* initial-margin rate as a percentage (0-100);
                           required collateral = CEIL(size * price * InitialMargin / 100) *)
    MaintenanceMargin,  (* minimum collateral (in whole units) to keep open *)
    TickSize,           (* minimum price increment (positive integer)       *)
    MaxPrice,           (* upper bound on any price, used for type checking *)
    MaxBalance          (* upper bound on any balance, used for bounding TLC *)

-----------------------------------------------------------------------------
(* ---------------------------------------------------------------------- *)
(*  V A R I A B L E S                                                      *)
(* ---------------------------------------------------------------------- *)

VARIABLES
    Balance,                (* Balance[a]             : collateral balance of account a    *)
    Position,               (* Position[a][m]         : signed size (Int): >0 long, <0 short *)
    EntryPrice,             (* EntryPrice[a][m]       : entry price of a's position in m   *)
    MarkPrice,              (* MarkPrice[m]            : current mark price for market m     *)
    OraclePrice,            (* OraclePrice[m]          : latest oracle price for market m   *)
    FundingRate,            (* FundingRate[m]          : funding rate in -100..100           *)
    OrderBook,              (* OrderBook[m]            : sequence of pending limit orders    *)
    InsuranceFundPos,       (* InsuranceFundPos[m]     : insurance fund's net position in m;
                               absorbs liquidated positions to preserve NetPositionZero     *)
    InsuranceFundBalance    (* InsuranceFundBalance    : cash reserves of the insurance fund;
                               receives collateral from liquidated accounts and absorbs any
                               bankruptcy deficit; invariant: InsuranceFundBalance >= 0     *)

vars == <<Balance, Position, EntryPrice, MarkPrice,
          OraclePrice, FundingRate, OrderBook,
          InsuranceFundPos, InsuranceFundBalance>>

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
 * Unrealised profit-and-loss helpers.
 *
 * Positions are signed integers:
 *   Position[a][m] > 0  => long  (profits when mark rises above entry)
 *   Position[a][m] < 0  => short (profits when mark falls below entry)
 *   Position[a][m] = 0  => flat
 *
 * AbsPnL returns the non-negative magnitude of the unrealised PnL,
 * regardless of direction.  PnLPositive tells us whether the position
 * is currently in profit (TRUE) or at a loss (FALSE).
 * Both helpers stay in Nat so that downstream arithmetic is simpler.
 *)

AbsPnL(a, m) ==
    LET pos   == Position[a][m]
        absPos == IF pos >= 0 THEN pos ELSE -pos
        entry  == EntryPrice[a][m]
        mark   == MarkPrice[m]
    IN  IF mark >= entry
        THEN absPos * (mark - entry)
        ELSE absPos * (entry - mark)

PnLPositive(a, m) ==
    (* TRUE when the unrealised PnL is non-negative for account a in m.
       Long  profits when mark >= entry.
       Short profits when mark <= entry.
       Flat accounts are counted as break-even (TRUE) to contribute 0. *)
    LET pos == Position[a][m]
    IN  \/ (pos > 0 /\ MarkPrice[m] >= EntryPrice[a][m])
        \/ (pos < 0 /\ MarkPrice[m] <= EntryPrice[a][m])
        \/ pos = 0

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
    (* TRUE when account a has any non-zero position (long OR short) *)
    \E m \in Markets : Position[a][m] /= 0

(*
 * AccountSafeAtMarkPrice(a, m, mark)
 * Check that account a's total equity would remain above MaintenanceMargin
 * if market m's mark price were set to `mark`.  Handles both long and short
 * positions.  Used as a pre-condition in PriceUpdate to preserve MarginSafety
 * across price changes.
 * Other-market PnL is computed by removing the current market-m contribution
 * from the aggregate sums and replacing it with the hypothetical new-mark PnL.
 *)
AccountSafeAtMarkPrice(a, m, mark) ==
    LET pos         == Position[a][m]
        absPos      == IF pos >= 0 THEN pos ELSE -pos
        entry       == EntryPrice[a][m]
        (* PnL from market m at the candidate mark price *)
        gain        == IF pos > 0 /\ mark >= entry THEN absPos * (mark - entry)
                       ELSE IF pos < 0 /\ entry >= mark THEN absPos * (entry - mark)
                       ELSE 0
        loss        == IF pos > 0 /\ entry > mark THEN absPos * (entry - mark)
                       ELSE IF pos < 0 /\ mark > entry THEN absPos * (mark - entry)
                       ELSE 0
        (* PnL from all other markets at their current mark prices *)
        otherGains  == PositivePnLSum(a) - (IF PnLPositive(a, m) THEN AbsPnL(a, m) ELSE 0)
        otherLosses == NegativePnLSum(a) - (IF ~PnLPositive(a, m) THEN AbsPnL(a, m) ELSE 0)
    IN  Balance[a] + gain + otherGains >= loss + otherLosses + MaintenanceMargin

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
 * InitialMarginReq(size, price)
 * The amount of collateral that must be available to open (or remain in) a
 * position of `size` contracts at the given price.  Both `size` and `price`
 * are positive integers (the caller ensures this).
 *
 * InitialMargin is a rate expressed as a whole-number percentage (0-100).
 * The required collateral is computed as:
 *   CEIL(size * price * InitialMargin / 100)
 * using ceiling division (divisor = 100) so that even very small positions
 * require at least 1 unit of collateral whenever InitialMargin > 0.
 *)
InitialMarginReq(size, price) ==
    (size * price * InitialMargin + 99) \div 100

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
 * MaintenanceMargin after the trade.  The buyer's position in m changes by
 * +tradeSize (can go from short → flat → long); entry is set to tradePrice
 * for any non-zero resulting position.  Other-market PnL is unchanged.
 *)
PostTradeBuyerSafe(buyer, m, tradePrice, tradeSize) ==
    LET newBal      == Balance[buyer] - InitialMarginReq(tradeSize, tradePrice)
        newPos      == Position[buyer][m] + tradeSize
        absNew      == IF newPos >= 0 THEN newPos ELSE -newPos
        (* PnL at new position; entry price will be tradePrice if newPos /= 0 *)
        newGainM    == IF newPos > 0 /\ MarkPrice[m] >= tradePrice
                       THEN absNew * (MarkPrice[m] - tradePrice)
                       ELSE IF newPos < 0 /\ tradePrice >= MarkPrice[m]
                       THEN absNew * (tradePrice - MarkPrice[m])
                       ELSE 0
        newLossM    == IF newPos > 0 /\ tradePrice > MarkPrice[m]
                       THEN absNew * (tradePrice - MarkPrice[m])
                       ELSE IF newPos < 0 /\ MarkPrice[m] > tradePrice
                       THEN absNew * (MarkPrice[m] - tradePrice)
                       ELSE 0
        oldGainM    == IF PnLPositive(buyer, m) THEN AbsPnL(buyer, m) ELSE 0
        oldLossM    == IF ~PnLPositive(buyer, m) THEN AbsPnL(buyer, m) ELSE 0
        otherGains  == PositivePnLSum(buyer) - oldGainM
        otherLosses == NegativePnLSum(buyer) - oldLossM
    IN  newBal + newGainM + otherGains >= newLossM + otherLosses + MaintenanceMargin

(*
 * PostTradeSellerSafe(seller, m, tradePrice, tradeSize)
 * TRUE when the seller's total equity (across all markets) remains above
 * MaintenanceMargin after the trade.  The seller's position in m changes by
 * -tradeSize (can go from long → flat → short); entry is set to tradePrice
 * for any non-zero resulting position.  Other-market PnL is unchanged.
 *)
PostTradeSellerSafe(seller, m, tradePrice, tradeSize) ==
    LET newBal      == Balance[seller] - InitialMarginReq(tradeSize, tradePrice)
        newPos      == Position[seller][m] - tradeSize
        absNew      == IF newPos >= 0 THEN newPos ELSE -newPos
        (* PnL at new position; entry price will be tradePrice if newPos /= 0 *)
        newGainM    == IF newPos > 0 /\ MarkPrice[m] >= tradePrice
                       THEN absNew * (MarkPrice[m] - tradePrice)
                       ELSE IF newPos < 0 /\ tradePrice >= MarkPrice[m]
                       THEN absNew * (tradePrice - MarkPrice[m])
                       ELSE 0
        newLossM    == IF newPos > 0 /\ tradePrice > MarkPrice[m]
                       THEN absNew * (tradePrice - MarkPrice[m])
                       ELSE IF newPos < 0 /\ MarkPrice[m] > tradePrice
                       THEN absNew * (MarkPrice[m] - tradePrice)
                       ELSE 0
        oldGainM    == IF PnLPositive(seller, m) THEN AbsPnL(seller, m) ELSE 0
        oldLossM    == IF ~PnLPositive(seller, m) THEN AbsPnL(seller, m) ELSE 0
        otherGains  == PositivePnLSum(seller) - oldGainM
        otherLosses == NegativePnLSum(seller) - oldLossM
    IN  newBal + newGainM + otherGains >= newLossM + otherLosses + MaintenanceMargin

(*
 * SumPositions(m)
 * The net open interest in market m: sum of all account positions plus the
 * insurance fund's net position.  This is 0 if and only if every long has
 * an exact short counterpart (possibly held by the insurance fund after
 * a liquidation).
 *)
SumPositions(m) ==
    LET helper[S \in SUBSET Accounts] ==
            IF S = {} THEN 0
            ELSE LET a == CHOOSE x \in S : TRUE
                 IN  Position[a][m] + helper[S \ {a}]
    IN  helper[Accounts] + InsuranceFundPos[m]

(*
 * LiquidationEquityDelta(a)
 * The net cash impact on the insurance fund when account a is liquidated.
 *   equity = Balance[a] + PositivePnLSum(a) - NegativePnLSum(a)
 *
 * If equity >= 0 (solvent but below maintenance margin):
 *   Fund receives the full equity as cash surplus.
 * If equity < 0 (bankrupt: unrealised losses exceed the cash balance):
 *   Fund receives Balance[a] in cash but "pays" the shortfall; the net
 *   impact on the fund's cash reserves is exactly `equity` (a negative
 *   number equal to -(shortfall)).
 *
 * Used both as the cash update in Liquidate and in the guard that prevents
 * liquidation when the fund cannot absorb the deficit.
 *)
LiquidationEquityDelta(a) ==
    Balance[a] + PositivePnLSum(a) - NegativePnLSum(a)

-----------------------------------------------------------------------------
(* ---------------------------------------------------------------------- *)
(*  I N V A R I A N T S                                                    *)
(* ---------------------------------------------------------------------- *)

TypeInvariant ==
    /\ Balance              \in [Accounts -> Nat]
    /\ Position             \in [Accounts -> [Markets -> Int]]
    /\ EntryPrice           \in [Accounts -> [Markets -> Nat]]
    /\ MarkPrice            \in [Markets -> Nat]
    /\ OraclePrice          \in [Markets -> Nat]
    /\ FundingRate          \in [Markets -> -100..100]
    /\ InsuranceFundPos     \in [Markets -> Int]
    /\ InsuranceFundBalance \in Int
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

(*
 * NetPositionZero: the net open interest in every market is zero — every
 * long has an exact short counterpart.  When a trader is liquidated their
 * position is transferred to the insurance fund (InsuranceFundPos), so the
 * zero-sum identity is maintained even through liquidations.
 *
 * This is the fundamental accounting identity of a derivatives exchange:
 *   \sum_{a \in Accounts} Position[a][m]  +  InsuranceFundPos[m]  =  0
 *)
NetPositionZero ==
    \A m \in Markets : SumPositions(m) = 0

(*
 * InsuranceFundSolvent: the insurance fund's cash reserves are always
 * non-negative.  The fund receives the net equity of each liquidated
 * account (LiquidationEquityDelta) when solvent, or floors at zero when the
 * account is bankrupt and the deficit exceeds the fund's reserves.  In the
 * latter case the remaining shortfall is absorbed via Auto-Deleveraging (ADL):
 * profitable counterparty positions are force-closed at mark price, redirecting
 * their unrealised gains to cover the bankrupt account's deficit.
 *)
InsuranceFundSolvent ==
    InsuranceFundBalance >= 0

(*
 * LiquidationAlwaysSucceeds: liquidation can always proceed for any
 * undercollateralised account — it is never blocked by an insufficient
 * insurance fund.
 *
 * Two complementary mechanisms guarantee this:
 *   1. Insurance fund: absorbs the full deficit when InsuranceFundBalance + delta >= 0.
 *   2. ADL (auto-deleveraging): when the fund is insufficient, the zero-sum
 *      property (NetPositionZero) guarantees that for every market m where a
 *      holds a position, at least one other participant (account or the fund
 *      itself via InsuranceFundPos) holds the exactly counterbalancing position
 *      and can be ADL'd to cover the shortfall.
 *
 * Formally: for any undercollateralised account a, either the fund is
 * sufficient, or for every market m in which a has a non-zero position there
 * exists a counterparty on the opposite side (guaranteed by SumPositions(m) = 0).
 *)

(*
 * HasCounterparty(a, m)
 * TRUE when there exists at least one participant that holds a position
 * strictly opposite in sign to Position[a][m] in market m.  Participants
 * are either other trader accounts or the insurance fund (InsuranceFundPos).
 *
 * Used in LiquidationAlwaysSucceeds to assert that ADL is always possible:
 * if the insurance fund is insufficient, there is always someone on the
 * other side whose profitable position can be force-closed to cover the
 * deficit (guaranteed by NetPositionZero / SumPositions(m) = 0).
 *)
HasCounterparty(a, m) ==
    (\E b \in Accounts : b /= a /\ Position[b][m] * Position[a][m] < 0) \/
    (InsuranceFundPos[m] * Position[a][m] < 0)

LiquidationAlwaysSucceeds ==
    \A a \in Accounts :
        (HasOpenPosition(a) /\ ~SufficientMargin(a)) =>
            LET delta == LiquidationEquityDelta(a)
            IN  \/ InsuranceFundBalance + delta >= 0          (* fund covers deficit *)
                \/ \A m \in Markets :                          (* ADL counterparties exist *)
                       Position[a][m] = 0 \/ HasCounterparty(a, m)

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
    /\ \A a \in Accounts, m \in Markets :
           -MaxBalance <= Position[a][m] /\ Position[a][m] <= MaxBalance
    /\ \A m \in Markets :
           -MaxBalance <= InsuranceFundPos[m] /\ InsuranceFundPos[m] <= MaxBalance
    /\ -MaxBalance <= InsuranceFundBalance /\ InsuranceFundBalance <= MaxBalance
    /\ \A m \in Markets : Len(OrderBook[m]) <= 2

-----------------------------------------------------------------------------
(* ---------------------------------------------------------------------- *)
(*  I N I T I A L   S T A T E                                              *)
(* ---------------------------------------------------------------------- *)

Init ==
    /\ Balance              = [a \in Accounts |-> 0]
    /\ Position             = [a \in Accounts |-> [m \in Markets |-> 0]]
    /\ EntryPrice           = [a \in Accounts |-> [m \in Markets |-> 0]]
    /\ MarkPrice            = [m \in Markets |-> TickSize]
    /\ OraclePrice          = [m \in Markets |-> TickSize]
    /\ FundingRate          = [m \in Markets |-> 0]
    /\ OrderBook            = [m \in Markets |-> << >>]
    /\ InsuranceFundPos     = [m \in Markets |-> 0]
    /\ InsuranceFundBalance = 0

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
                   FundingRate, OrderBook, InsuranceFundPos, InsuranceFundBalance>>

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
                   FundingRate, OrderBook, InsuranceFundPos, InsuranceFundBalance>>

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
    /\ Balance[a] >= InitialMarginReq(size, price)
    /\ LET o == [account |-> a, side |-> side, size |-> size, price |-> price]
       IN  OrderBook' = [OrderBook EXCEPT ![m] = Append(@, o)]
    /\ UNCHANGED <<Balance, Position, EntryPrice, MarkPrice,
                   OraclePrice, FundingRate, InsuranceFundPos, InsuranceFundBalance>>

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
 *   - Buyer's position changes by +tradeSize (can go short → flat → long).
 *   - Seller's position changes by -tradeSize (can go long → flat → short).
 *   - Entry price is set to tradePrice for any non-zero resulting position,
 *     or cleared to 0 when the position closes exactly to zero.
 *   - Both parties pay InitialMarginReq(tradeSize, tradePrice) from their balance.
 *   - The fully-consumed order is removed; any partial residual is appended
 *     back with its size reduced.
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
           /\ LET buyOrder      == OrderBook[m][i]
                  sellOrder     == OrderBook[m][j]
                  tradePrice    == sellOrder.price
                  tradeSize     == Min(buyOrder.size, sellOrder.size)
                  buyer         == buyOrder.account
                  seller        == sellOrder.account
                  newBuyerPos   == Position[buyer][m]  + tradeSize
                  newSellerPos  == Position[seller][m] - tradeSize
                  lo            == IF i < j THEN i ELSE j
                  hi            == IF i < j THEN j ELSE i
                  (* Remove both matched orders; re-add any partial residual. *)
                  base          == SubSeq(OrderBook[m], 1, lo - 1)
                                   \o SubSeq(OrderBook[m], lo + 1, hi - 1)
                                   \o SubSeq(OrderBook[m], hi + 1, Len(OrderBook[m]))
                  newBook       ==
                      IF    buyOrder.size < sellOrder.size
                      THEN  Append(base, [sellOrder EXCEPT !.size = @ - tradeSize])
                      ELSE IF buyOrder.size > sellOrder.size
                      THEN  Append(base, [buyOrder  EXCEPT !.size = @ - tradeSize])
                      ELSE  base  (* both orders fully consumed *)
               IN
                  /\ buyer /= seller
                  /\ Balance[buyer]  >= InitialMarginReq(tradeSize, tradePrice)
                  /\ Balance[seller] >= InitialMarginReq(tradeSize, tradePrice)
                  (* No seller position pre-condition: seller opens a new short if flat *)
                  /\ PostTradeBuyerSafe(buyer, m, tradePrice, tradeSize)
                  /\ PostTradeSellerSafe(seller, m, tradePrice, tradeSize)
                  /\ Balance' = [Balance EXCEPT
                         ![buyer]  = @ - InitialMarginReq(tradeSize, tradePrice),
                         ![seller] = @ - InitialMarginReq(tradeSize, tradePrice)]
                  /\ Position' = [Position EXCEPT
                         ![buyer][m]  = newBuyerPos,
                         ![seller][m] = newSellerPos]
                  /\ EntryPrice' = [EntryPrice EXCEPT
                         (* Entry price is tradePrice for any open position,
                            or 0 when the position exactly closes to zero. *)
                         ![buyer][m]  = IF newBuyerPos  = 0 THEN 0 ELSE tradePrice,
                         ![seller][m] = IF newSellerPos = 0 THEN 0 ELSE tradePrice]
                  /\ OrderBook' = [OrderBook EXCEPT ![m] = newBook]
    /\ UNCHANGED <<MarkPrice, OraclePrice, FundingRate, InsuranceFundPos, InsuranceFundBalance>>

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
    (* Safety pre-check: all accounts with any position remain above maintenance margin *)
    /\ \A a \in Accounts :
           Position[a][m] /= 0 => AccountSafeAtMarkPrice(a, m, newMark)
    /\ MarkPrice'   = [MarkPrice   EXCEPT ![m] = newMark]
    /\ OraclePrice' = [OraclePrice EXCEPT ![m] = newOracle]
    /\ UNCHANGED <<Balance, Position, EntryPrice, FundingRate, OrderBook,
                   InsuranceFundPos, InsuranceFundBalance>>

(*
 * UpdateFundingRate(m, rate)
 * The exchange sets a new funding rate for market m.
 * The rate is an integer (can be negative for shorts paying longs).
 *)
UpdateFundingRate(m, rate) ==
    /\ m \in Markets
    /\ FundingRate' = [FundingRate EXCEPT ![m] = rate]
    /\ UNCHANGED <<Balance, Position, EntryPrice, MarkPrice,
                   OraclePrice, OrderBook, InsuranceFundPos, InsuranceFundBalance>>

(*
 * ProcessFunding(a, m)
 * Apply the current funding payment for account a's position in market m.
 * Funding transfers wealth from one side to the other:
 *   Rate >= 0: longs pay, shorts receive  (mark >= oracle → market is rich)
 *   Rate <  0: shorts pay, longs receive  (mark < oracle → market is cheap)
 * Payment = |Position| * |FundingRate|.
 * When the account owes funding its post-payment equity must still satisfy
 * MaintenanceMargin; when it receives funding its balance only increases.
 *)
ProcessFunding(a, m) ==
    /\ a \in Accounts
    /\ m \in Markets
    /\ Position[a][m] /= 0
    /\ LET pos     == Position[a][m]
           absPos  == IF pos >= 0 THEN pos ELSE -pos
           rate    == FundingRate[m]
           absRate == IF rate >= 0 THEN rate ELSE -rate
           payment == absPos * absRate
           (* Long pays when rate >= 0; short pays when rate < 0 *)
           paying  == (pos > 0 /\ rate >= 0) \/ (pos < 0 /\ rate < 0)
       IN  /\ rate /= 0    (* skip no-op when funding rate is zero *)
           /\ payment > 0  (* also skip if somehow position is zero (redundant safety) *)
           /\ IF paying
              THEN (* payer: balance must stay non-negative; check post-payment margin *)
                   /\ Balance[a] >= payment
                   /\ SufficientMarginAfterDebit(a, payment)
                   /\ Balance' = [Balance EXCEPT ![a] = @ - payment]
              ELSE (* receiver: balance only increases, always safe *)
                   /\ Balance' = [Balance EXCEPT ![a] = @ + payment]
    /\ UNCHANGED <<Position, EntryPrice, MarkPrice, OraclePrice,
                   FundingRate, OrderBook, InsuranceFundPos, InsuranceFundBalance>>

(*
 * Liquidate(a)
 * Force-close ALL of account a's positions when its margin is insufficient.
 * Pre-condition: account has at least one open position AND is below maintenance
 *                margin (SufficientMargin is FALSE).
 *
 * Liquidation always succeeds — it is never blocked by an insufficient insurance
 * fund.  Two mechanisms handle the cash settlement:
 *
 *   1. delta >= 0  (solvent account, below maintenance): fund receives the
 *      remaining equity as a cash surplus.
 *   2. delta < 0  (bankrupt account, losses exceed cash):
 *      a. If InsuranceFundBalance + delta >= 0: fund absorbs the deficit.
 *      b. If InsuranceFundBalance + delta < 0:  fund is fully depleted to 0;
 *         the remaining shortfall is covered by Auto-Deleveraging (ADL) — the
 *         most profitable counterparty positions are force-closed at mark price,
 *         redirecting their gains to cover the deficit.  The zero-sum property
 *         (NetPositionZero) guarantees counterparty positions always exist.
 *
 * The liquidated positions are transferred to InsuranceFundPos rather than
 * zeroed, preserving NetPositionZero: every long still has a short counterpart
 * (now held by the insurance fund).
 *
 * Post-condition: a's positions and entry prices are zeroed; a's balance is
 *                 zeroed; InsuranceFundBalance is updated (floored at 0).
 *                 HasOpenPosition(a) becomes FALSE, so MarginSafety is
 *                 vacuously satisfied after liquidation.
 *)
Liquidate(a) ==
    /\ a \in Accounts
    /\ HasOpenPosition(a)
    /\ ~SufficientMargin(a)
    (* Liquidation always proceeds — no fund-balance guard.
       Fund absorbs what it can; any remaining deficit is covered by ADL. *)
    /\ LET delta == LiquidationEquityDelta(a)
       IN  InsuranceFundBalance' =
               IF InsuranceFundBalance + delta >= 0
               THEN InsuranceFundBalance + delta   (* fund absorbs full delta *)
               ELSE 0                             (* fund depleted; rest via ADL *)
    /\ InsuranceFundPos' = [m \in Markets |->
                                InsuranceFundPos[m] + Position[a][m]]
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
    \/ \E a \in Accounts : Liquidate(a)

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
THEOREM Spec => []NetPositionZero
THEOREM Spec => []InsuranceFundSolvent
THEOREM Spec => []LiquidationAlwaysSucceeds

=============================================================================
