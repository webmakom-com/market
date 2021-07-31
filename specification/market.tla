------------------------------- MODULE Market -------------------------------
EXTENDS     FiniteSetsExt, FiniteSets, MarketHelpers, Naturals, 
            Sequences, SequencesExt

CONSTANT    ExchAccount,    \* Set of all accounts
            Coin,           \* Set of all coins
            Denominator,    \* Set of all possible denominators. 
                            \* Precision of fractions is defined by 
                            \* denominator constant.
            Amount
           
VARIABLE    accounts,       \* Exchange Accounts
            ask,            \* Ask Coin
            bid,            \* Bid Coin       
            drops,          \* Drops of Liquidity (tokens)
            limits,         \* Limit Order Books
            pools,          \* AMM pool Curves
            stops           \* Stop Loss Order Books
            

Limit == INSTANCE Limit
Stop == INSTANCE Stop

ASSUME Denominator \in Nat
-----------------------------------------------------------------------------
(***************************** Type Declarations ***************************)

NoVal == CHOOSE v : v \notin Nat
NoCoin == CHOOSE c : c \notin Coin

\* All exchange rates are represented as numerator/denominator tuples
ExchRateType == {<<a, b>> : a \in {1 .. 50}, b \in { 1 .. Denominator }}

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
(* Each account has ordered sequences of stop and limit positions for each *)
(* coin balance.  The sequence sums are limited to a maximum of the        *)
(* bid coin account balance.                                               *) 
(*                                                                         *)
(* Cosmos-SDK type                                                         *)
(*                                                                         *)
(* https://docs.cosmos.network/v0.39/modules/auth/03_types.html#stdsigndoc *)
(* type AccountType struct {                                               *) 
(*      balance:    uint256                                                *)
(*      poaitions:                                                         *)
(* }                                                                       *)
(***************************************************************************)
AccountType ==
[
    balance: Nat,
    positions: [Coin -> <<Seq(PositionType), Seq(PositionType)>>]
]

CoinType == {{c} : c \in Coin}
Pairs == { {a, b} : a \in CoinType, b \in CoinType }
PairType == { pair \in Pairs : Cardinality(pair) > 1 }
AccountPlusCoin == {<<e, c>> : e \in ExchAccount, c \in CoinType}
AccountPlusPair == {<<e, p>> : e \in ExchAccount, p \in PairType}
PairPlusCoin == { <<pair, coin>> \in PairType \X CoinType : coin \in pair }


TypeInvariant ==
    /\  accounts \in [AccountPlusCoin -> AccountType]
    /\  ask \in CoinType
    /\  bid \in CoinType
    /\  drops \in [AccountPlusPair -> Nat]
    \* Alternative Declaration
    \* [Pair \X Coin -> Sequences]
    /\  limits \in [PairPlusCoin -> Seq(PositionType)]
    /\  pools \in [PairPlusCoin -> Nat]
    /\  stops \in [PairPlusCoin -> Seq(PositionType)]
    

(************************** Variable Initialization ************************)       
        
MarketInit ==  
    /\  accounts = [
            apc \in AccountPlusCoin |-> 
                [
                    balance |-> 0,
                    positions |-> 
                        [ c \in Coin |-> 
                        << <<>>, <<>> >>
                ]
            ]   
        ]
    \*  Tracks the Current Ask Coin
    /\  ask = NoCoin
    \*  Tracks the Current Bid Coin
    /\  bid = NoCoin
    /\  drops = [app \in AccountPlusPair |-> 0]
    /\  limits = [ppc \in PairPlusCoin |-> <<>>]
    /\  pools = [ppc \in PairPlusCoin |-> 0]
    /\  stops = [ppc \in PairPlusCoin |-> <<>>]





(***************************** Step Functions ****************************)
\* Deposit coin into exchange ExchAccount
\* acct: ExchAccount
\* c: Coin
\* amt: amt of Coin
Deposit(acct, c, amt) ==    
    /\  accounts' = [accounts EXCEPT ![<<acct, c>>].balance = @ + amt]
    /\  UNCHANGED << ask, bid, drops, limits, pools, stops >>

\* Withdraw coin from exchange ExchAccount
\* acct: ExchAccount
\* c: Coin
\* amt: amt of Coin
Withdraw(acct, c, amt) ==
    /\  accounts[<<acct, c>>].balance >= amt
    /\  accounts' = [accounts EXCEPT ![<<acct, c>>].balance = @ - amt]
    /\  UNCHANGED << ask, bid, drops, limits, pools, stops >> 

(***************************************************************************)
(* Open(acct, askCoin, bidCoin, pos)                                       *)
(*                                                                         *)
(* Open a position on the exchange.  The position is placed in the         *)
(* corresponding user exchange account bid coin sequence and the exchange  *)
(* order book defined by the type, bid coin and ask coin.                  *)
(*                                                                         *) 
(* Parameters                                                              *)
(* acct<AccountType>: Exchange Account                                     *)
(* askCoin<Coin>: Ask Coin                                                 *)
(* bidCoin<Coin>: Bid Coin                                                 *)
(* pos<PositionType>: Position                                             *)
(***************************************************************************)
Open(acct, askCoin, bidCoin, type, pos) == 
    IF pos.amt > accounts[<<acct, bidCoin>>].balance
    THEN UNCHANGED << accounts, ask, bid, drops, limits, pools, stops >>
    ELSE
    LET 
        t == IF type = "limit" THEN 0 ELSE 1
        balance == accounts[<<acct, bidCoin>>].balance
        posSeqs == accounts[<<acct, bidCoin>>].positions[askCoin]
    IN 
    /\  IF  SumSeq(posSeqs[t]) + pos.amt <= balance
        THEN
        /\  ask' = askCoin
        /\  bid' = bidCoin   
            \* IF type is limit?  
        /\  IF  t = 0
            THEN
            /\  LET igt == IGT(posSeqs[0], pos) IN
                IF igt = {} 
                THEN 
                    accounts' = 
                        [accounts EXCEPT ![<<acct, bidCoin>>].positions[askCoin] =
                        <<Append(pos, @[0]),@[1]>>]
                ELSE
                    accounts' =
                        [accounts EXCEPT ![<<acct, bidCoin>>].positions[askCoin] =
                        <<InsertAt(@[0], Min(igt), pos),@[1]>>]
            /\  LET igt == IGT(limits[<<{askCoin, bidCoin}, bidCoin>>], pos) IN
                IF igt = {}
                THEN    limits' =
                    [limits EXCEPT ![<<{askCoin, bidCoin}, bidCoin>>] =
                    Append(pos, @)]
                ELSE    limits' =
                    [limits EXCEPT ![<<{askCoin, bidCoin}, bidCoin>>] =
                    InsertAt(@, Min(igt), pos)]
            /\  UNCHANGED << drops, pools, stops >>
            \* ELSE type is stops
            ELSE
            /\  LET ilt == ILT(posSeqs[1], pos) IN
                IF ilt = {} 
                THEN 
                    accounts' = 
                        [accounts EXCEPT ![<<acct, bidCoin>>].positions[askCoin] =
                        <<@[0], Append(pos, @[1])>>]
                ELSE
                    accounts' =
                        [accounts EXCEPT ![<<acct, bidCoin>>].positions[askCoin] =
                        <<@[0], InsertAt(@[1], Max(ilt), pos)>>]
            /\  LET ilt == ILT(stops[<<{askCoin, bidCoin}, bidCoin>>], pos) IN
                IF ilt = {}
                THEN    stops' =
                    [stops EXCEPT ![<<{askCoin, bidCoin}, bidCoin>>] =
                    Append(pos, @)]
                ELSE    stops' =
                    [stops EXCEPT ![<<{askCoin, bidCoin}, bidCoin>>] =
                    InsertAt(@, Max(ilt), pos)]
            /\  UNCHANGED << drops, limits, pools >>
        \* ELSE Balance is too low
        ELSE    UNCHANGED << accounts, ask, bid, drops, limits, pools, stops >>

Close(acct, askCoin, bidCoin, type, i) ==
    LET 
        t == IF type = "limit" THEN 0 ELSE 1
        balance == accounts[<<acct, bidCoin>>].balance
        posSeqs == accounts[<<acct, bidCoin>>].positions[askCoin][t]
        pos == posSeqs[i]
    IN  IF t = 0
        THEN       
            /\  limits' =
                    [limits EXCEPT ![<<{askCoin, bidCoin}, bidCoin>>] =
                    Remove(posSeqs[0], pos)]
            /\  accounts' = [ 
                    accounts EXCEPT ![<<acct, bidCoin>>].positions[askCoin] = 
                    <<Remove(@[0], pos),@[1]>>
                ]
            /\  UNCHANGED << stops, pools >> 
        ELSE    
            /\  stops' = [
                    stops EXCEPT ![<<{askCoin, bidCoin}, bidCoin>>] =
                    Remove(posSeqs[1], pos)
                ]
            /\  accounts' = [ 
                    accounts EXCEPT ![<<acct, bidCoin>>].positions[askCoin] = 
                    <<@[0], Remove(@[1], pos)>>
                ]
            /\  UNCHANGED << limits, pools >>


Provision(acct, pair, amt) ==

LET \* This is a hack below need to find out how to do this without making a set of 1 element
    strong == CHOOSE strong \in pair : TRUE
    weak == CHOOSE weak \in pair \ {strong} : TRUE
    poolExchrate == << pools[<<pair, weak>>], pools[<<pair, strong>>] >>
    balStrong == accounts[<<acct, strong>>].balance
    balWeak == accounts[<<acct, weak>>].balance
    bidStrong == 
        IF  amt > balStrong
            THEN    balStrong
            ELSE    amt
    bidWeak == 
    IF  pools[<<pair, strong>>] > 0
    THEN
        (bidStrong * pools[<<pair, weak>>]) \div pools[<<pair, strong>>]
    ELSE
        IF amt <= balWeak
            THEN    balWeak
            ELSE    amt
        
IN
    IF bidWeak > 0
    THEN
        IF bidStrong > 0
        THEN
    /\  pools' = [ pools EXCEPT
            ![<<pair, weak>>] = @ + bidWeak,
            ![<<pair, strong>>] = @ + bidStrong
        ]
    /\  drops' = [ drops EXCEPT 
            ![<<acct, pair>>] = @ + bidStrong 
        ]
    /\  accounts' = [ accounts EXCEPT
            ![<<acct, weak>>].balance = @ - bidWeak,
            ![<<acct, strong>>].balance = @ - bidStrong
        ]
    /\ UNCHANGED << ask, bid, limits, stops >>
    ELSE UNCHANGED << accounts, ask, bid, drops, limits, pools, stops >>
    ELSE UNCHANGED << accounts, ask, bid, drops, limits, pools, stops >>

Liquidate(acct, pair, amt) ==
\* Qualifying condition
/\  LET 
        pool == pools[pair]
        strong == CHOOSE strong \in pair : TRUE
        weak == CHOOSE weak \in pair \ {strong} : TRUE
        bidStrong == amt
        bidWeak == 
        IF pools[<<pair, strong>>] > 0
        THEN (amt * pools[<<pair, weak>>]) \div pools[<<pair, strong>>]
        ELSE amt
    IN
        IF  drops[<<acct, pair>>] < amt
        THEN UNCHANGED << accounts, ask, bid, drops, limits, pools, stops >>
        ELSE
        /\  accounts' = [ accounts EXCEPT
                ![<<acct, weak>>].balance = @ + bidWeak,
                ![<<acct, strong>>].balance = @ + bidStrong
            ]
        /\  pools' = [ pools EXCEPT 
                ![<<pair, strong>>] = @ - @ * (amt \div pools[<<pair, weak>>]),
                ![<<pair, weak>>] = @ - amt
            ]
        
        /\ drops' = [ drops EXCEPT 
            ![<<acct, pair>>] = @ - amt ]
        /\ UNCHANGED << accounts, ask, bid, drops, limits, pools, stops >>
                
-----------------------------------------------------------------------------
               
Next == \/ \E   acct \in ExchAccount,
                pair \in PairType, 
                amt \in Amount :        \/  Provision(acct, pair, amt)
                                        \/  Liquidate(acct, pair, amt)
        \/ \E   acct \in ExchAccount,
                coin \in CoinType,
                amt \in Amount :        \/  Deposit(acct, coin, amt)
                                        \/  Withdraw(acct, coin, amt)
        \/  \E   acct \in ExchAccount :
            \E   pair \in PairType : 
            \E   bidCoin \in pair :
            \E   amount \in Amount : 
            \E   askCoin \in pair \ bidCoin :
            \E   type \in {"limit", "stop"} :
            \E   exchrate \in ExchRateType : 
            \/  /\  Open(
                            acct,
                            askCoin,
                            bidCoin,
                            type,
                            [
                                acct: acct,
                                amt: amount,
                                exchrate: exchrate
                            ]
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
\* Last modified Sat Jul 31 14:27:53 CDT 2021 by Charles Dusek
\* Last modified Tue Jul 06 15:21:40 CDT 2021 by cdusek
\* Last modified Tue Apr 20 22:17:38 CDT 2021 by djedi
\* Last modified Tue Apr 20 14:11:16 CDT 2021 by charlesd
\* Created Tue Apr 20 13:18:05 CDT 2021 by charlesd
