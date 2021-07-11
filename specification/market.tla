------------------------------- MODULE market -------------------------------
EXTENDS     Naturals, Sequences, SequencesExt

CONSTANT    Account,    \* Set of all accounts
            Coin,       \* Set of all coins
            Denominator \* Set of all possible denominators. Precision of 
                        \* fractions is defined by denominator constant.
           
VARIABLE    limitBooks, \* Limit Order Books
            stopBooks,  \* Stop Loss Order Books
            bonds,      \* AMM Bond Curves
            orderQ,     \* Sequenced queue of orders
            drops       \* Drops of Liquidity (tokens)

ASSUME Denominator \subseteq Nat
-----------------------------------------------------------------------------
(***************************** Type Declarations ***************************)

NoVal == CHOOSE v : v \notin Nat

\* All exchange rates are represented as numerator/denominator tuples
ExchRateType == <<a \in Nat, b \in Denominator>>

\* Pairs of coins are represented as couple sets
\* { {{a, b}: b \in Coin \ {a}}: b \in Coin} 
PairType == {{a, b}: a \in Coin, b \in Coin \ {a}}

(**************************************************************************)
(* Pair plus Coin Type                                                    *)
(*                                                                        *)
(* Each pair is a set with two coins.  Each pair may have variables that  *)
(* depend on both the pair (set of two coins) as well as one of the coins *)
(* associated with that particular pair                                   *)
(**************************************************************************)
PairPlusCoin == { <<pair, coin>> \in Pair \X Coin: coin \in pair} 

(***************************************************************************)
(* Position Type                                                           *)
(*                                                                         *)
(* The position type is the order book record that is maintained when a    *)
(* limit order has an unfulfilled outstanding amount                       *)
(*                                                                         *)
(* id <uint256>: Identifier of the position                                *) 
(* amount <Nat>: Amount of Bid Coin                                        *)
(* limit <ExchRateType>: Lower Bound of the Upper Sell Region              *)
(* loss <ExchRateType>: Upper Bound of the Lower Sell Region               *)
(*                                                                         *)
(* Cosmos-SDK types                                                        *)
(* https://docs.cosmos.network/v0.39/modules/auth/03_types.html#stdsigndoc *)
(*                                                                         *)
(* type PositionType struct {                                              *) 
(*      id:         uint256                                                *)
(*      Amount      CoinDec                                                *)
(*      limit       Dec                                                    *)
(*      loss        Dec                                                    *)
(* }                                                                       *)
(***************************************************************************)
PositionType == [
    id: Nat,
    amount: Nat,
    exchrate: ExchRateType
]

(***************************** Exchange Account ****************************)
(* The Exchange Account holds active exchange balances with their          *)
(* associated order positions.                                             *)
(*                                                                         *)
(* Example Position                                                        *)
(*                                                                         *)
(* Limit Order: designated by a single position with limit set to          *)
(* lower bound of upper sell region and loss set to 0.                     *)
(*                                                                         *)
(* [amount: Nat, bid: Coin positions: {                                    *)
(*      ask: Coin                                                          *)
(*      limit: ExchrateType                                                *)
(*      loss: 0                                                            *)
(*  }]                                                                     *)
(*                                                                         *)
(* Market Order: designated by a single position with limit and loss set   *)
(* to zero.  Setting limit to zero means no limit.                         *)
(*                                                                         *)
(* [amount: Nat, bid: Coin positions: {                                    *)
(*      ask: Coin                                                          *)
(*      limit: 0                                                           *)
(*      loss: 0                                                            *)
(*  }]                                                                     *)                                                             
(*                                                                         *)
(*                                                                         *)
(* Cosmos-SDK type                                                         *)
(*                                                                         *)
(* https://docs.cosmos.network/v0.39/modules/auth/03_types.html#stdsigndoc *)
(* type AccountType struct {                                               *) 
(*      id          uint64                                                 *)
(*      balances    Array                                                  *)
(* }                                                                       *)
(***************************************************************************)

AccountType == [
    \* The balance and positions of each denomination of coin in an
    \* exchange account are represented by the record type below
    SUBSET [
        \* Denomination of Coin balance
        bidDenom: Coin,
        \* Balances are represented as Natural number
        balance: Nat,
        \* Positions are sequenced by ExchRate
        \*
        \* Sum of amounts in sequence of positions for a particular Ask 
        \* Coin must be lower than or equal to the accounts denom balance
        \*
        \* [AskCoin -> << Limits, Stops >>]
        positions: [Coin -> <<Seq(PositionType), Seq(PositionType)>>]
    ]
] 

TypeInvariant ==
    /\  accounts \in [Account -> AccountType]
    \* Alternative Declaration
    \* [Pair \X Coin -> Sequences]
    /\  bonds \in [PairPlusCoin -> Nat]
    /\  drops \in [Pair -> Nat]
    /\  limits \in [PairPlusCoin -> Seq(PositionType)]
    /\  orderQ \in [Pair -> Seq(Order)]
    /\  stops \in [PairPlusCoin -> Seq(PositionType)]

(************************** Variable Initialization ************************)       
        
MarketInit ==  
    /\ accounts \in [Account |-> [
        balances: {}
    ]]
    /\ drops \in [Pair |-> Nat]
    \* order books bid sequences
    /\ books = [ppc \in PairPlusCoin |-> <<>>]
    \* liquidity balances for each pair
    /\ bonds = [ppc \in PairPlusCoin |-> NoVal]
    /\ orderQ = [p \in Pair |-> <<>>]

(***************************** Helper Functions ****************************)

\* Nat tuple (numerator/denominator) inequality helper functions
\* All equalities assume Natural increments
GT(a, b) ==     IF a[1]*b[2] > a[2]*b[1] THEN TRUE ELSE FALSE

GTE(a, b) ==    IF a[1]*b[2] >= a[2]*b[1] THEN TRUE ELSE FALSE 

LT(a, b) ==     IF a[1]*b[2] < a[2]*b[1] THEN TRUE ELSE FALSE

LTE(a, b) ==    IF a[1]*b[2] <= a[2]*b[1] THEN TRUE ELSE FALSE

\* This division needs
BondAskAmount(bondAskBal, bondBidBal, bidAmount) ==
    (bondAskBal * bidAmount) \div bondBidBal

Stronger(pair)    ==  CHOOSE c \in pair :  bonds[c] <= bond[pair \ {c}]

(***************************************************************************)
(* Max amount that Bond pool may sell of ask coin without                  *)
(* executing an ask coin book limit order.                                 *)
(*                                                                         *)
(* Expression origin:                                                      *)
(* bondAsk / bondBid = erate                                               *)
(* d(bondAsk)/d(bondBid) = d(erate)                                        *)
(* d(bondAsk)/d(bondBid) = d(bondAsk)/d(bondBid)                           *)
(* d(bondAsk) = d(bondBid) * d(bondAsk)/d(bondBid)                         *)
(* d(bondAsk) = d(bondBid) * d(erate)                                      *)
(*                                                                         *)
(* Integrate over bondAsk on lhs and bondBid & erate on rhs then           *)
(* substitute and simplify                                                 *)
(*                                                                         *)
(* MaxBondBid = bondAsk(initial) - bondAsk(final)                          *)
(* bondAsk(final) = bondBid(initial) * erate(final)^2 / erate(initial)     *)
(*                                                                         *)
(* MaxBondBid =                                                            *)
(* bondAsk(initial) - bondBid(initial) * erate(final) ^ 2 / erate(initial) *)
(*                                                                         *)
(* erate(intial) = bondAsk / bondBid                                       *)
(*                                                                         *)
(* MaxBondBid =                                                            *)
(* bondAsk(initial) -                                                      *)
(* bondBid(initial) ^ 2 * erate(final) ^ 2 /                               *)
(* [(bondAsk(initial)/bondBid(initial)]                                    *)
(***************************************************************************)
MaxBondBid(erateFinal, bondNumerator, bondDenominator) ==  
    \* MaxBondBid = 
    \* bondAsk(initial) - 
    \* bondBid(initial)^2 * erate(final) ^ 2 / 
    \* erate(initial)
    bondNumerator - bondDenominator^2 * erateFinal^2 \div 
    (bondNumerator / bondDenominator)


Reconcile(p) ==
    /\  ctl = "Reconcile"
    /\  LET
            strong == Strong(p)
            weak == c \in p : c # strong
        IN  LET
            bondStrong ==   bonds[p][strong]
            bondWeak ==     bonds[p][weak]
            limitStrong ==  Head(limits[p][strong])
            limitWeak ==    Head(limits[p][weak])
            stopStrong ==   Head(stops[p][strong])
            stopWeak ==     Head(stops[p][weak])
        IN  LET
            bondExchrate ==         
                <<bondWeak, bondStrong>>
            limitWeakInverseExchrate ==
                <<limitsWeak.exchrate[1], limitsWeak.exchrate[0]>>
            stopWeakInverseExchrate == 
                <<stopsWeak.exchrate[1], stopsWeak.exchrate[0]>>
        IN
            CASE    stopWeakInverseExchrate.LT(bondExchrate)    ->
                CASE limitStrong.exchrate = bondExchrate
                THEN \* In this case the exchrate does not change if equal amounts of ask
                     \* and bid coins are simulataneously exchanged.
                     \* AMM may exchange up the to least amount of the limitStrong or
                     \* the stopWeak orders.
                    LET least == 
                        CHOOSE least \in { limitStrong, stopWeak } : least.amount <
                        { limitStrong.amount, stopWeak.amount } \ least.amount
                    IN
                        /\ limits' = [limits EXCEPT ![p][strong] = 
                            IF Head(@).amount = least.amount
                            THEN \* Remove limit record from head of limit sequence
                                Tail(@)
                            ELSE \* Replace head limit record with one that has updated
                                 \* amount 
                                Append (
                                    [
                                        id: Head(@).id
                                        amount: Head(@).amount - least.amount
                                        exchrate: Head(@).exchrate
                                    ], 
                                    Tail(@)
                                 )
                         
                        
                    
                ELSE
            []      limitStrong.exchrate.LT(bondExchrate)       ->
                LET bondBid == MaxBondBid(limitStrong.exchrate, bondWeak, bondStrong)      
            []      stopStrong.exchrate.GT(bondExch             ->
                IF limitWeakInverseExchrate.GT(bondExchrate)
                THEN
                ELSE
            []      limitWeakInverseExchrate.GT(bondExchrate)   ->
            

(***************************** Step Functions ****************************)
\* Deposit coin into exchange account
Deposit(a, c, amount) ==    
    LET record == { d \in accounts[a] : d.bidDenom }
    IN
        IF record = {}
        THEN 
            accounts' = [accounts EXCEPT ![a] = UNION {
                @, 
                [
                    bidDenom: c,
                    balance: amount,
                    positions: [d \in Coin \ c |-> << <<>>, <<>> >>
                ]
            }
        ELSE
            accounts' = [accounts EXCEPT ![a] = UNION {
                @ / record,
                [
                    bidDenom: c,
                    balance: amount + record.amount,
                    positions: record.positions
                ]
            }

\* Withdraw coin from exchange account
Withdraw(a, c) ==

\* Optional syntax
(* LET all_limit_orders == Add your stuff in here *)
(* IN {x \in all_limit_orders: x.bid # x.ask} *)
\* p = pair
\* c = bid coin
\* a = account
SubmitOrder(a) == 
    /\  \E o \in Order : 
        /\  o.bid # o.ask
        /\  orderQ' = [orderQ EXCEPT ![{o.bid, o.ask}] = Append(@, o)]
    /\  UNCHANGED <<books, bonds>>

Provision(pair) ==
    \* Use Input constant to give ability to limit amounts input  
    \E r \in Nat : r \in Input 
        LET bond == bonds[pair]
        IN
            LET c == Weaker(pair)
                d == pair \ c
            IN
                /\  bonds' = [ bonds EXCEPT 
                        ![pair][d] = 
                            @ + 
                            @ * 
                            (r / bonds[pair][c]),
                        ![pair][c] = @ + r
                    ]
                /\  drops' = [ drops EXCEPT 
                        ![pair] = @ + r 
                    ]
                /\ UNCHANGED << books, orderQ >>

Liquidate(pair) ==  
    \E r \in Nat : 
        \* Qualifying condition
        /\  r < drops[pair]
        /\  LET 
                bond == bonds[pair]
            IN
                LET 
                    c == Weaker(pair)
                    d == pair \ c
                IN
                    /\  bonds' = [ bonds EXCEPT 
                            ![pair][d] = @ - @ * 
                                (r / bonds[pair][c]),
                            ![pair][c] = @ - r
                        ]
                    
                    /\ drops' = [ drops EXCEPT 
                        ![pair] = @ - r ]
                    /\ UNCHANGED << books, orderQ >>
                       
(***************************************************************************)
(* Process Order inserts a new limit and stop positions into the limit and *)
(* stop sequences of the ask coin                                          *)
(***************************************************************************)
ProcessOrder(p) ==

    (*************************** Enabling Condition ************************)
    (* Order queue is not empty                                            *)
    (***********************************************************************)
    /\ orderQ[pair] # <<>>
    
    (*************************** Internal Variables ************************)
    (* Internal variables are used to track intermediate changes to books  *)
    (* bonds on copy of the working state                                  *)
    (***********************************************************************)
    /\ LET o == Head(orderQ[pair]) IN
        LET (*************************** Books *****************************)
            limitBid == limits[pair][o.bid]
            stopBid == stops[pair][o.bid]
            
            (*************************** Bonds *****************************)
            bondAsk == bonds[pair][o.ask]
            bondBid == bonds[pair][o.bid]
            
            (*************************** Order *****************************)
            orderAmt == o.amount
            
        IN  
            \* indices gt than active exchange

            (***************************************************************)
            (* Define Process() to allow for loop back                     *)
            (***************************************************************)
            LET Process ==
                \* Run this on the limits
                LET igt ==
                    {i in 0..Len(limitBid): limitBid[i].exchrate > o.exchrate}
                IN \*Check following line!
                    IF igt = {} THEN 
                        /\ limits = [limits EXCEPT ![pair][o.bid] = Append(<<order>>, @)
                        /\ ctl' = "Bid"
                    ELSE limits' = [limits EXCEPT ![pair][o.bid] 
                        = InsertAt(@, Min(igt), order)] 
                
                \* Run this on the stops
                LET ilt ==
                    {i in 0..Len(stopBid): stopBid[i].exchrate < o.exchrate}
                IN \*Check following line!
                    IF ilt = {} THEN 
                        /\ [stops EXCEPT ![pair][o.bid] = Append(<<order>>, @)
                        /\ ctl' = "Strong"
                    ELSE stops' = [stops EXCEPT ![pair][o.bid] 
                        = InsertAt(@, Min(igt), order)]

\* Explore mutual recursion, but for now, will use strong and weak to differentiate
ProcessStrong(p) ==
    /\  ctl = "strong" 
    /\  LET strong = bonds[p][c \in p : \A {bonds[p][d] : d \in p} <= bonds[p][c]] IN
            LET 
                strongLimitHead = Head(limits[p][strong])
                weakStopHead = Head(stops[p][{c \in p : c # strong}])
            IN 
                CASE    strongLimitHead.exchrate.GT(weakStopHead.exchrate) ->
                []      strongLimitHead.exchrate.LT(weakStopHead.exchrate) ->
                []      strongLimitHead.exchrate = weakStopHead.exchrate ->


ProcessWeak(p) ==
    /\ ctl = "weak"
    /\  LET weak = bonds[p][c \in p : \A {bonds[p][d] : d \in p} >= bonds[p][c]] IN
            LET 
                weakLimitHead = Head(limits[p][strong])
                strongStopHead = Head(stops[p][{c \in p : c # strong}])
            IN 
                CASE    weakLimitHead.exchrate.GT(strongStopHead.exchrate) ->
                []      weakLimitHead.exchrate.LT(strongStopHead.exchrate) ->
                []      weakLimitHead.exchrate = strongStopHead.exchrate ->

ProcessMid(p) ==
    /\ ctl = "mid"
    /\  LET 
            strong = bonds[p][c \in p : \A {bonds[p][d] : d \in p} <= bonds[p][c]]
            weak = bonds[p][c \in p : \A {bonds[p][d] : d \in p} >= bonds[p][c]]
        IN  
            
                
Next == \/ \E p: p == {c, d} \in Pair : c != d :    \/ ProcessOrder(p)
                                                    \/ ProcessAsk(p)
                                                    \/ ProcessBid(p)
                                                    \/ Provision(p)
                                                    \/ Liquidate(p)
        \/ SubmitOrder

=============================================================================
\* Modification History
\* Last modified Sat Jul 10 22:43:47 CDT 2021 by Charles Dusek
\* Last modified Tue Jul 06 15:21:40 CDT 2021 by cdusek
\* Last modified Tue Apr 20 22:17:38 CDT 2021 by djedi
\* Last modified Tue Apr 20 14:11:16 CDT 2021 by charlesd
\* Created Tue Apr 20 13:18:05 CDT 2021 by charlesd
