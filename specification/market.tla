------------------------------- MODULE market -------------------------------
EXTENDS     Naturals, Sequences, SequencesExt

CONSTANT    ExchAccount,    \* Set of all accounts
            Coin,       \* Set of all coins
            Denominator \* Set of all possible denominators. Precision of 
                        \* fractions is defined by denominator constant.
           
VARIABLE    limitBooks,     \* Limit Order Books
            stopBooks,      \* Stop Loss Order Books
            bonds,          \* AMM Bond Curves
            orderQ,         \* Sequenced queue of orders
            pairPlusStrong, \* Current Pair plus Strong Coin 
            drops           \* Drops of Liquidity (tokens)

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
PairPlusCoin == { <<pair, coin>> \in PairType \X Coin: coin \in pair } 

(***************************************************************************)
(* Position Type                                                           *)
(*                                                                         *)
(* The position type is the order book record that is maintained when a    *)
(* limit order has an unfulfilled outstanding amount                       *)
(*                                                                         *)
(* ExchAccount <uint256>: Identifier of the position                       *) 
(* amount <Nat>: Amount of Bid Coin                                        *)
(* exchrate <ExchRateType>: The Limit or Loss set-point                    *)
(*                                                                         *)
(* Cosmos-SDK types                                                        *)
(* https://docs.cosmos.network/v0.39/modules/auth/03_types.html#stdsigndoc *)
(*                                                                         *)
(* type PositionType struct {                                              *) 
(*      ExchAccount:    uint256                                                *)
(*      Amount      CoinDec                                                *)
(*      exchrate    Dec                                                    *)
(* }                                                                       *)
(***************************************************************************)
PositionType == [
    ExchAccount: ExchAccount,
    amount: Nat,
    exchrate: ExchRateType
]

(***************************** Exchange ExchAccount ************************)
(* The Exchange ExchAccount holds active exchange balances with their      *)
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
(*      ExchAccount     uint64                                             *)
(*      balances    Array                                                  *)
(* }                                                                       *)
(***************************************************************************)

AccountType == [
    \* The balance and positions of each denomination of coin in an
    \* exchange ExchAccount are represented by the record type below
    Coin -> [
        \* Balances are represented as Natural number
        balance: Nat,
        \* Positions are sequenced by ExchRate
        \*
        \* Sum of amounts in sequence of positions for a particular Ask 
        \* Coin must be lower than or equal to the accounts denom balance
        \*
        \* [AskCoin -> << Limits [0], Stops [1]>>]
        positions: [Coin -> <<Seq(PositionType), Seq(PositionType)>>]
    ]
] 

TypeInvariant ==
    /\  accounts \in [ExchAccount -> AccountType]
    \* Alternative Declaration
    \* [Pair \X Coin -> Sequences]
    /\  bonds \in [PairPlusCoin -> Nat]
    /\  drops \in [Pair -> Nat]
    /\  limits \in [PairPlusCoin -> Seq(PositionType)]
    /\  orderQ \in [Pair -> Seq(Order)]
    /\  pairPlusStrong \in PairPlusCoin
    /\  stops \in [PairPlusCoin -> Seq(PositionType)]

(************************** Variable Initialization ************************)       
        
MarketInit ==  
    /\  accounts = [
            a \in ExchAccount |-> [
                c \in Coin |-> [
                    balance: 0,
                    positions: [
                        Coin |-> << <<>>, <<>> >>
                    ]
                ] 
            ]   
        ]
    /\ drops = [p \in Pair |-> Nat]
    \* order books bid sequences
    /\ books = [ppc \in PairPlusCoin |-> <<>>]
    \* liquidity balances for each pair
    /\ bonds = [ppc \in PairPlusCoin |-> NoVal]
    /\ orderQ = [p \in Pair |-> <<>>]
    /\ pairPlusStrong = <<>>

Stronger(pair)    ==  CHOOSE c \in pair :  bonds[c] <= bond[pair \ {c}]

(***************************** Step Functions ****************************)
\* Deposit coin into exchange ExchAccount
\* a: ExchAccount
\* c: Coin
\* amount: Amount of Coin
Deposit(a, c, amount) ==    
    /\  accounts' = [accounts EXCEPT ![a][c].balance = @ + amount]
    /\  UNCHANGED << >>

\* Withdraw coin from exchange ExchAccount
\* a: ExchAccount
\* c: Coin
\* amount: Amount of Coin
Withdraw(a, c, amount) ==
    /\  accounts[a][c].balance >= amount
    /\  accounts' = [accounts EXCEPT ![a][c].balance = @ - amount]
    /\  UNCHANGED << >> 

\* Optional syntax
(* LET all_limit_orders == Add your stuff in here *)
(* IN {x \in all_limit_orders: x.bid # x.ask} *)
SubmitPosition(a, ask, bid, type, pos) == 
    LET 
        t == IF type = "limit" THEN 0 ELSE 1
        balance == accounts[a][bid].balance
        posSeqs == accounts[a][bid].positions[ask]
    IN 
    /\  IF      SumSeq(posSeqs[t]) + pos.amount <= balance
        THEN    accounts' = [accounts EXCEPT ![a][bid].positions[ask] = 
        
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
    (***********************************************************************)
    (* Set strong coin                                                     *)
    (***********************************************************************)
    /\ strong' = <<p, Strong(p)>>
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
    
    /\ ctl' = "WeakStop""
    /\ UNCHANGED << >>


                        
                


ProcessWeak(p) ==
    /\ ctl = "weak"
    /\  LET weak = bonds[p][c \in p : \A {bonds[p][d] : d \in p} >= bonds[p][c]] IN
            LET 
                weakLimitHead = Head(limits[p][strong])
                strongStopHead = Head(stops[p][{c \in p : c # strong}])
            IN 
                

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
        \/ \E a \in ExchAccount : 
           \E {ask, bid} \in Pair : ask != bid :
           \E type \in {"limit", "stop"} : 
           \E pos \in Position :                    \/ SubmitPosition(
                                                            a,
                                                            ask,
                                                            bid,
                                                            type,
                                                            pos
                                                        )

=============================================================================
\* Modification History
\* Last modified Sat Jul 17 11:59:49 CDT 2021 by Charles Dusek
\* Last modified Tue Jul 06 15:21:40 CDT 2021 by cdusek
\* Last modified Tue Apr 20 22:17:38 CDT 2021 by djedi
\* Last modified Tue Apr 20 14:11:16 CDT 2021 by charlesd
\* Created Tue Apr 20 13:18:05 CDT 2021 by charlesd
