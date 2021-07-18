------------------------------- MODULE Market -------------------------------
EXTENDS     MarketHelpers, Naturals, Sequences, SequencesExt

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
(*      ExchAccount:    uint256                                            *)
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
        u == IF type = "limit" THEN 1 ELSE 1
        balance == accounts[a][bid].balance
        posSeqs == accounts[a][bid].positions[ask]
    IN 
    /\  IF  SumSeq(posSeqs[t]) + pos.amount <= balance
        THEN     
            IF  type = "limit"
            THEN
            /\  LET igt == IGT(posSeqs[0], pos) IN
                IF igt = {} 
                THEN 
                    accounts' = 
                        [accounts EXCEPT ![a][bid].positions[ask] =
                        <<Append(pos, @[0]),@[1]>>]
                ELSE
                    accounts' =
                        [accounts EXCEPT ![a][bid].positions[ask] =
                        <<InsertAt(@[0], Min(igt), pos),@[1]>>]
            /\  LET igt == IGT(limits[<<{ask, bid}, bid>>], pos) IN
                IF igt = {}
                THEN    limits' =
                    [limits EXCEPT ![<<{ask, bid}, bid>>] =
                    Append(pos, @)]
                ELSE    limits' =
                    [limits EXCEPT ![<<{ask, bid}, bid>>] =
                    InsertAt(@, Min(igt), pos)]
            \* ELSE Stops
            ELSE
            /\  LET ilt == ILT(posSeqs[1], pos) IN
                IF ilt = {} 
                THEN 
                    accounts' = 
                        [accounts EXCEPT ![a][bid].positions[ask] =
                        <<@[0], Append(pos, @[1])>>]
                ELSE
                    accounts' =
                        [accounts EXCEPT ![a][bid].positions[ask] =
                        \* Should this be Max(ilt)?
                        <<@[0], InsertAt(@[1], Min(ilt), pos)>>]
            /\  LET ilt == ILT(stops[<<{ask, bid}, bid>>], pos) IN
                IF ilt = {}
                THEN    stops' =
                    [stops EXCEPT ![<<{ask, bid}, bid>>] =
                    Append(pos, @)]
                ELSE    stops' =
                    [stops EXCEPT ![<<{ask, bid}, bid>>] =
                    \* Should this be Max(ilt)?
                    InsertAt(@, Min(ilt), pos)]
        ELSE    UNCHANGED << everything >>

\* Need to add ClosePosition

Provision(pair) ==
    \* Use Input constant to give ability to limit amounts input  
    \E r \in Nat :
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
                
Next == \/ \E p: p == {c, d} \in Pair : c != d :    \/ Provision(p)
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
\* Last modified Sat Jul 17 21:45:28 CDT 2021 by Charles Dusek
\* Last modified Tue Jul 06 15:21:40 CDT 2021 by cdusek
\* Last modified Tue Apr 20 22:17:38 CDT 2021 by djedi
\* Last modified Tue Apr 20 14:11:16 CDT 2021 by charlesd
\* Created Tue Apr 20 13:18:05 CDT 2021 by charlesd
