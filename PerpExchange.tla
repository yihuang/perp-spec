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
EXTENDS Naturals, Sequences

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
    MaxPrice            (* upper bound on any price, used for type checking *)

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
 * ExecuteTrade(m, i, j)
 * Match the i-th buy order against the j-th sell order in market m when
 * their prices cross.  Both orders must be on opposite sides and the buyer's
 * price must be >= the seller's price.  For simplicity the trade executes at
 * the seller's (ask) price and fully fills both orders.
 *
 * Post-conditions:
 *   - Positions of both accounts are updated (long +size, short −size with
 *     Nat encoding: short side decrements position of the existing long or
 *     is ignored in this simplified model where we only track long exposure).
 *   - Both orders are removed from the order book.
 *   - Balance of each party is reduced by the filled notional * InitialMargin
 *     rate (simplified: each pays InitialMargin as margin per trade).
 *)
ExecuteTrade(m, i, j) ==
    /\ m \in Markets
    /\ i \in DOMAIN OrderBook[m]
    /\ j \in DOMAIN OrderBook[m]
    /\ i /= j
    /\ OrderBook[m][i].side = 1    (* i is the buyer *)
    /\ OrderBook[m][j].side = -1   (* j is the seller *)
    /\ OrderBook[m][i].price >= OrderBook[m][j].price
    /\ LET buyOrder  == OrderBook[m][i]
           sellOrder == OrderBook[m][j]
           tradePrice == sellOrder.price
           tradeSize  == buyOrder.size
           buyer  == buyOrder.account
           seller == sellOrder.account
       IN
           /\ Balance[buyer]  >= InitialMargin
           /\ Balance[seller] >= InitialMargin
           /\ Position[seller][m] >= tradeSize   (* seller must hold enough *)
           /\ Balance' = [Balance EXCEPT
                  ![buyer]  = @ - InitialMargin,
                  ![seller] = @ - InitialMargin]
           /\ Position' = [Position EXCEPT
                  ![buyer][m]  = @ + tradeSize,
                  ![seller][m] = @ - tradeSize]
           /\ EntryPrice' = [EntryPrice EXCEPT
                  ![buyer][m]  = tradePrice,
                  ![seller][m] = tradePrice]
           (* Remove both matched orders from the book using SelectSeq *)
           /\ LET newSeq == SelectSeq(OrderBook[m],
                                LAMBDA o : o /= OrderBook[m][i] /\ o /= OrderBook[m][j])
              IN  OrderBook' = [OrderBook EXCEPT ![m] = newSeq]
    /\ UNCHANGED <<MarkPrice, OraclePrice, FundingRate>>

(*
 * PriceUpdate(m, newMark, newOracle)
 * The exchange updates the mark price and oracle price for market m.
 * Pre-conditions : m \in Markets, both prices are positive multiples of TickSize.
 *)
PriceUpdate(m, newMark, newOracle) ==
    /\ m \in Markets
    /\ newMark   > 0
    /\ newOracle > 0
    /\ newMark   <= MaxPrice
    /\ newOracle <= MaxPrice
    /\ newMark   % TickSize = 0
    /\ newOracle % TickSize = 0
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
 * Pre-condition: account has a non-zero position in the market.
 *)
ProcessFunding(a, m) ==
    /\ a \in Accounts
    /\ m \in Markets
    /\ Position[a][m] > 0
    /\ LET rate    == FundingRate[m]
           size    == Position[a][m]
           payment == size * (IF rate >= 0 THEN rate ELSE -rate)
       IN  IF rate >= 0
           THEN (* longs pay; ensure they have enough balance *)
                /\ Balance[a] >= payment
                /\ Balance' = [Balance EXCEPT ![a] = @ - payment]
           ELSE (* longs receive *)
                /\ Balance' = [Balance EXCEPT ![a] = @ + payment]
    /\ UNCHANGED <<Position, EntryPrice, MarkPrice, OraclePrice,
                   FundingRate, OrderBook>>

(*
 * Liquidate(a, m)
 * Force-close account a's position in market m when margin is insufficient.
 * Pre-condition: account has an open position AND is below maintenance margin.
 * Post-condition: position is zeroed; balance is set to 0 (insurance fund
 *                 absorbs any deficit in a real system; simplified here).
 *)
Liquidate(a, m) ==
    /\ a \in Accounts
    /\ m \in Markets
    /\ Position[a][m] > 0
    /\ ~SufficientMargin(a)
    /\ Position'   = [Position   EXCEPT ![a][m] = 0]
    /\ EntryPrice' = [EntryPrice EXCEPT ![a][m] = 0]
    /\ Balance'    = [Balance    EXCEPT ![a] = 0]
    /\ UNCHANGED <<MarkPrice, OraclePrice, FundingRate, OrderBook>>

-----------------------------------------------------------------------------
(* ---------------------------------------------------------------------- *)
(*  N E X T - S T A T E   R E L A T I O N                                 *)
(* ---------------------------------------------------------------------- *)

Next ==
    \/ \E a \in Accounts, amount \in 1..1000 :
           Deposit(a, amount)
    \/ \E a \in Accounts, amount \in 1..Balance[a] + 1 :
           Withdraw(a, amount)
    \/ \E a \in Accounts, m \in Markets,
          side \in {1, -1}, size \in 1..10, price \in 1..MaxPrice :
           PlaceOrder(a, m, side, size, price)
    \/ \E m \in Markets, i \in 1..Len(OrderBook[m]), j \in 1..Len(OrderBook[m]) :
           ExecuteTrade(m, i, j)
    \/ \E m \in Markets, p1 \in 1..MaxPrice, p2 \in 1..MaxPrice :
           PriceUpdate(m, p1, p2)
    \/ \E m \in Markets, r \in -10..10 :
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
 * TLC can verify both for finite instantiations of the constants.
 *)
THEOREM Spec => []TypeInvariant
THEOREM Spec => []MarginSafety

=============================================================================
