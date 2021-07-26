------------------------------- MODULE Market -------------------------------
EXTENDS     FiniteSetsExt, FiniteSets, MarketHelpers, Naturals, 
            Sequences, SequencesExt

CONSTANT    ExchAccount,    \* Set of all accounts
            Coin,           \* Set of all coins
            Denominator,    \* Set of all possible denominators. 
                            \* Precision of fractions is defined by 
                            \* denominator constant.
            Amount          \* Amounts
           
VARIABLE    accounts,       \* Exchange Accounts
            ask,            \* Ask Coin
            bid,            \* Bid Coin       
            limits,         \* Limit Order Books
            stops,          \* Stop Loss Order Books
            pools,          \* AMM pool Curves
            drops           \* Drops of Liquidity (tokens)

Limit == INSTANCE Limit
Stop == INSTANCE Stop

ASSUME Denominator \in Nat
ASSUME Amount \in SUBSET Nat
-----------------------------------------------------------------------------
(***************************** Type Declarations ***************************)

NoVal == CHOOSE v : v \notin Nat
NoCoin == CHOOSE c : c \notin Coin

\* All exchange rates are represented as numerator/denominator tuples
ExchRateType == {<<a, b>> : a \in Nat, b \in { 1 .. Denominator }}

\* Pairs of coins are represented as couple sets
\* { {{a, b}: b \in Coin \ {a}}: b \in Coin} 
Pairs == { {a, b} : a \in Coin, b \in Coin }

PairType == { pair \in Pairs : Cardinality(pair) > 1 }

(**************************************************************************)
(* Pair plus Coin Type                                                    *)
(*                                                                        *)
(* Each pair is a set with two coins.  Each pair may have variables that  *)
(* depend on both the pair (set of two coins) as well as one of the coins *)
(* associated with that particular pair                                   *)
(**************************************************************************)
PairPlusCoin == { <<pair, coin>> \in PairType \X Coin : coin \in pair }

(***************************************************************************)
(* Position Type                                                           *)
(*                                                                         *)
(* The position type is the order book record that is maintained when a    *)
(* limit or stop order has an unfulfilled outstanding amount               *)
(*                                                                         *)
(* The position type is defined by the parent sequence.  The position may  *)
(* either be a limit or stop type.                                         *)                  
(*                                                                         *)
(* Position record fields                                                  *)
(* acct: Position Owner                                                    *) 
(* amt: Amount of Bid Coin                                                 *)
(* exchrate: The Limit or Stop Loss set-point                              *)
(*                                                                         *)
(* Market Order: designated by a single position with limit set to zero.   *)  
(* Setting limit to zero means no limit.                                   *)
(*                                                                         *)
(*  {                                                                      *)
(*      acct: ExchAccount                                                  *)
(*      amt: Nat                                                           *)
(*      exchrate: 0                                                        *)
(*  }                                                                      *)                                                             
(*                                                                         *)
(* Cosmos-SDK types                                                        *)
(* https://docs.cosmos.network/v0.39/modules/auth/03_types.html#stdsigndoc *)
(*                                                                         *)
(* type PositionType struct {                                              *) 
(*      acct:       uint256                                                *)
(*      amt:        CoinDec                                                *)
(*      exchrate:   Dec                                                    *)
(* }                                                                       *)
(***************************************************************************)
PositionType == [
    acct: ExchAccount,
    amt: Nat,
    exchrate: ExchRateType
]

(***************************** Exchange Account ****************************)
(* The Exchange Account holds active exchange balances with their          *) 
(* associated order positions.                                             *)
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
AccountType ==
[
    balance: Nat,
    positions: [Coin -> <<Seq(PositionType), Seq(PositionType)>>]
]

AccountPlusCoin == {<<e, c>> : e \in ExchAccount, c \in Coin}

TypeInvariant ==
    /\  accounts \in [AccountPlusCoin -> AccountType]
    /\  ask \in Coin
    /\  bid \in Coin
    /\  drops \in [PairType -> Nat]
    \* Alternative Declaration
    \* [Pair \X Coin -> Sequences]
    /\  limits \in [PairPlusCoin -> Seq(PositionType)]
    /\  pools \in [PairPlusCoin -> Nat]
    /\  stops \in [PairPlusCoin -> Seq(PositionType)]
    

(************************** Variable Initialization ************************)       
        
MarketInit ==  
    /\  accounts = [
            a \in AccountPlusCoin |-> 
                [
                    balance |-> 0,
                    positions |-> 
                        [ c \in Coin |-> 
                        << <<>>, <<>> >>
                ]
            ]   
        ]
    \*  Tracks the Ask Coin
    /\  ask = NoCoin
    \*  Tracks the Bid Coin
    /\  bid = NoCoin
    /\  drops = [p \in PairType |-> 0]
    /\  limits = [ppc \in PairPlusCoin |-> <<>>]
    /\  pools = [ppc \in PairPlusCoin |-> 0]
    /\  stops = [ppc \in PairPlusCoin |-> <<>>]





(***************************** Step Functions ****************************)
\* Deposit coin into exchange ExchAccount
\* a: ExchAccount
\* c: Coin
\* amt: amt of Coin
Deposit(a, c, amt) ==    
    /\  accounts' = [accounts EXCEPT ![<<a, c>>].balance = @ + amt]
    /\  UNCHANGED << ask, bid, pools, drops, limits, stops >>

\* Withdraw coin from exchange ExchAccount
\* acct: ExchAccount
\* c: Coin
\* amt: amt of Coin
Withdraw(acct, c, amt) ==
    /\  accounts[<<acct, c>>].balance >= amt
    /\  accounts' = [accounts EXCEPT ![<<acct, c>>].balance = @ - amt]
    /\  UNCHANGED << ask, bid, drops, limits, pools, stops >> 

\* Optional syntax
(* LET all_limit_orders == Add your stuff in here *)
(* IN {x \in all_limit_orders: x.bidCoin # x.askCoin} *)
Open(a, askCoin, bidCoin, type, pos) == 
    LET 
        t == IF type = "limit" THEN 0 ELSE 1
        balance == accounts[<<a, bidCoin>>].balance
        posSeqs == accounts[<<a, bidCoin>>].positions[askCoin]
    IN 
    /\  IF  SumSeq(posSeqs[t]) + pos.amt <= balance
        THEN
        /\  ask' = askCoin
        /\  bid' = bidCoin     
        /\  IF  type = "limit"
            THEN
            /\  LET igt == IGT(posSeqs[0], pos) IN
                IF igt = {} 
                THEN 
                    accounts' = 
                        [accounts EXCEPT ![a][bidCoin].positions[askCoin] =
                        <<Append(pos, @[0]),@[1]>>]
                ELSE
                    accounts' =
                        [accounts EXCEPT ![a][bidCoin].positions[askCoin] =
                        <<InsertAt(@[0], Min(igt), pos),@[1]>>]
            /\  LET igt == IGT(limits[<<{askCoin, bidCoin}, bidCoin>>], pos) IN
                IF igt = {}
                THEN    limits' =
                    [limits EXCEPT ![<<{askCoin, bidCoin}, bidCoin>>] =
                    Append(pos, @)]
                ELSE    limits' =
                    [limits EXCEPT ![<<{askCoin, bidCoin}, bidCoin>>] =
                    InsertAt(@, Min(igt), pos)]
            /\  UNCHANGED << stops >>
            \* ELSE Stops
            ELSE
            /\  LET ilt == ILT(posSeqs[1], pos) IN
                IF ilt = {} 
                THEN 
                    accounts' = 
                        [accounts EXCEPT ![a][bidCoin].positions[askCoin] =
                        <<@[0], Append(pos, @[1])>>]
                ELSE
                    accounts' =
                        [accounts EXCEPT ![a][bidCoin].positions[askCoin] =
                        <<@[0], InsertAt(@[1], Max(ilt), pos)>>]
            /\  LET ilt == ILT(stops[<<{askCoin, bidCoin}, bidCoin>>], pos) IN
                IF ilt = {}
                THEN    stops' =
                    [stops EXCEPT ![<<{askCoin, bidCoin}, bidCoin>>] =
                    Append(pos, @)]
                ELSE    stops' =
                    [stops EXCEPT ![<<{askCoin, bidCoin}, bidCoin>>] =
                    InsertAt(@, Max(ilt), pos)]
            /\  UNCHANGED << limits >>
        ELSE    UNCHANGED <<>>

Close(acct, askCoin, bidCoin, type, i) ==
    LET 
        t == IF type = "limit" THEN 0 ELSE 1
        balance == accounts[acct][bidCoin].balance
        posSeqs == accounts[acct][bidCoin].positions[askCoin][t]
        pos == posSeqs[i]
    IN  IF t = 0
        THEN       
                /\  limits' =
                        [limits EXCEPT ![<<{askCoin, bidCoin}, bidCoin>>] =
                        Remove(posSeqs[0], pos)]
                /\  accounts' = [ 
                        accounts EXCEPT ![acct][bidCoin].positions[askCoin] = 
                        <<Remove(@[0], pos),@[1]>>
                    ]
                /\  UNCHANGED << stops, pools >> 
        ELSE    
                /\  stops' = [
                        stops EXCEPT ![<<{askCoin, bidCoin}, bidCoin>>] =
                        Remove(posSeqs[1], pos)
                    ]
                /\  accounts' = [ 
                        accounts EXCEPT ![acct][bidCoin].positions[askCoin] = 
                        <<@[0], Remove(@[1], pos)>>
                    ]


Provision(acct, pair, amt) ==
IF Cardinality(pair) > 1 THEN
    LET strong == Stronger(pair, pools)
        weak == pair \ strong
        poolExchrate == << pools[<<pair, weak>>], pools[<<pair, strong>>] >>
        balStrong == accounts[acct][strong].balance
        balWeak == accounts[acct][weak].balance
        bidWeak == 
            LET strongToWeak == (balStrong * pools[<<pair, weak>>]) \ pools[<<pair, strong>>]
            IN  IF  strongToWeak > balWeak
                THEN    balWeak
                ELSE    strongToWeak
        bidStrong ==
            (bidWeak * pools[<<pair, strong>>]) \ pools[<<pair, weak>>]
    IN
        /\  pools' = [ pools EXCEPT 
                ![<<pair, weak>>] = @ + bidWeak,
                ![<<pair, strong>>] = @ + bidStrong
            ]
        /\  drops' = [ drops EXCEPT 
                ![PairType] = @ + bidWeak 
            ]
        /\ UNCHANGED << limits, stops >>
ELSE UNCHANGED << accounts, ask, bid, drops, limits, pools, stops >>

Liquidate(acct, pair, amt) ==
IF Cardinality(pair) > 1 THEN
    \* Qualifying condition
    /\  amt < drops[pair]
    /\  LET 
            pool == pools[pair]
        IN
            LET 
                d == Stronger(pair, pools)
                c == pair \ d
            IN
                /\  pools' = [ pools EXCEPT 
                        ![pair][d] = @ - @ * (amt \ pools[pair][c]),
                        ![pair][c] = @ - amt
                    ]
                
                /\ drops' = [ drops EXCEPT 
                    ![pair] = @ - amt ]
                /\ UNCHANGED << limits, stops >>
ELSE UNCHANGED << accounts, ask, bid, drops, limits, pools, stops >>
                
-----------------------------------------------------------------------------
               
Next == \/ \E   acct \in ExchAccount,
                pair \in PairType, 
                amt \in Amount :        \/  Provision(acct, pair, amt)
                                        \/  Liquidate(acct, pair, amt)
        \/ \E   acct \in ExchAccount,
                coin \in Coin,
                amt \in Amount :        \/  Deposit(acct, coin, amt)
                                        \/  Withdraw(acct, coin, amt)
        \/  \E   acct \in ExchAccount : 
            \E   pair \in PairType : 
            \E   bidCoin \in pair :
            \E   askCoin \in pair \ bidCoin :
            \E   type \in {"limit", "stop"} : 
            \/  \E pos \in [
                    acct: acct,
                    amt: { 1 .. accounts[<<acct, bidCoin>>].balance },
                    exchrate: ExchRateType
                ] : 
                /\  Open(
                            acct,
                            askCoin,
                            bidCoin,
                            type,
                            pos
                        )
                /\  IF type = "limit"
                    THEN    Limit!Limit
                    ELSE    Stop!Stop
            \/    
                IF type = "limit" 
                THEN 
                    \E seq \in acct[{pair, bidCoin}][askCoin][0] :
                    /\  Len(seq) > 0
                    /\  \E  i \in Len(seq) :    
                        /\  Close(
                                acct,
                                askCoin,
                                bidCoin,
                                type,
                                i
                            )
                        /\  Limit!Limit
                            
                                 
                ELSE 
                    \E seq \in acct[{pair, bidCoin}][askCoin][1] :
                    /\  Len(seq) > 0
                    /\  \E  i \in Len(seq) :   
                        /\  Close(
                                acct,
                                askCoin,
                                bidCoin,
                                type,
                                i
                            )
                        /\  Stop!Stop

Spec == /\  MarketInit 
        /\ [][Next]_<<
                accounts,
                ask,
                bid,       
                limits,
                stops,
                pools,
                drops
           >>
-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
=============================================================================
\* Modification History
\* Last modified Sun Jul 25 20:52:38 CDT 2021 by Charles Dusek
\* Last modified Tue Jul 06 15:21:40 CDT 2021 by cdusek
\* Last modified Tue Apr 20 22:17:38 CDT 2021 by djedi
\* Last modified Tue Apr 20 14:11:16 CDT 2021 by charlesd
\* Created Tue Apr 20 13:18:05 CDT 2021 by charlesd
