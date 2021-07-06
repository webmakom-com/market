------------------------------- MODULE market -------------------------------
EXTENDS     Naturals, Sequences, SequencesExt

CONSTANT    Coin,       \* Set of all coins
            Denominator,\* Set of all possible denominators
            Input,      \* Set of all possible input amounts
            NOM,        \* NOM coin. Single Constant Collateral.
            Expiration  \* Set of all expirations
           
VARIABLE    limitBooks, \* Limit Order Books
            stopBooks,  \* Stop Loss Order Books
            bonds,      \* AMM Bond Curves
            orderQ, 
            drops

ASSUME Denominator \subseteq Nat
-----------------------------------------------------------------------------
(***************************** Type Declarations ***************************)

NoVal == CHOOSE v : v \notin Nat

\* Choose the highest natural number
UpperNatBound == CHOOSE v : v > \A n \in Nat \ v

\* All exchange rates are represented as numerator/denominator tuples
ExchRateType == {<<a, b>> : a \in Nat, b \in Denominator}

\* Max ExchRate
MAX == <<UpperNatBound, 1>>

\* Pairs of coins are represented as couple sets
\* { {{a, b}: b \in Coin \ {a}}: b \in Coin} 
PairType == {{a, b}: a \in Coin, b \in Coin \ {a}}

(***************************************************************************)
(* Position Type                                                           *)
(*                                                                         *)
(* The position type is the order book record that is maintained when a    *)
(* limit order has an unfulfilled outstanding amount                       *)
(*                                                                         *)
(* amount <Nat>: Amount of Bid Coin                                        *)
(* limit <ExchRateType>: Lower Bound of the Upper Sell Region              *)
(* loss <ExchRateType>: Upper Bound of the Lower Sell Region               *)
(*                                                                         *)
(* Cosmos-SDK types                                                        *)
(* https://docs.cosmos.network/v0.39/modules/auth/03_types.html#stdsigndoc *)
(*                                                                         *)
(* type PositionType struct {                                              *) 
(*      Order       uint64                                                 *)
(*      Amount      CoinDec                                                *)
(*      limit       Dec                                                    *)
(*      loss        Dec                                                    *)
(* }                                                                       *)
(***************************************************************************)
PositionType == [
    order: Nat,
    amount: Nat,
    limit: ExchRateType,
    loss: ExchRateType
]

(***************************** Exchange Account ****************************)
(* The Exchange Account holds active exchange balances with their          *)
(* associated order positions.                                             *)
(*                                                                         *)                                               *)
(*                                                                         *)
(* Pending Orders have one bid coin and may have many positions.           *)
(* Pending Orders may have any number of positions.                        *)
(* Each position corresponds to a single ask coin                          *)
(* There may only be one position per ask coin                             *)
(* A position defines the Limit and a Stop for a particular ask coin       *)
(* The bid coin amount is deposited to the Onomy Exchange                  *)
(* Each unique Pending Order corresponds to the amount deposited for thie  *)
(* order.                                                                  *)
(*                                                                         *)
(* Simple Limit Order: designated by a single position with limit set to   *)
(* lower bound of upper sell region and loss set to 0.                     *)
(*                                                                         *)
(* [amount: Nat, bid: Coin positions: {                                    *)
(*      ask: Coin                                                          *)
(*      limit: ExchrateType                                                *)
(*      loss: 0                                                            *)
(*  }]                                                                     *)                                                             
(*                                                                         *)
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
(* bidAmount <Nat>: Amount of Bid Coin                                     *)
(* bid <Coin>: Bid Coin                                                    *)
(* ask <Coin>: Ask Coin                                                    *)
(* exchrate <Real>: Exchange rate (ask/bid) limit                          *)
(*                                                                         *)
(* Cosmos-SDK type                                                         *)
(*                                                                         *)
(* https://docs.cosmos.network/v0.39/modules/auth/03_types.html#stdsigndoc *)
(* type LimitType struct {                                                 *) 
(*      Account     uint64                                                 *)
(*      Amount      CoinDec                                                *)
(*      bid         Coin                                                   *)
(*      ask         Coin                                                   *)
(*      exchrate    Dec                                                    *)
(* }                                                                       *)
(***************************************************************************)

AccountType == [
    id: Nat,
    balances: 
        SUBSET {
            amount: Coin
            \* Positions are sequenced by ExchRate
            \* One position per ExchRate
            \* Sum of amounts in sequence of positions for a particular Coin must
            \* be lower than or equal to the total order amount.
            positions: SUBSET PositionType
        }
]



(***************************************************************************)
(* Cosmos-SDK types (Same as Limit Order with exchrate max Dec             *)
(* https://docs.cosmos.network/v0.39/modules/auth/03_types.html#stdsigndoc *)
(*                                                                         *)
(* type OrderType struct {                                                 *) 
(*      Account     uint64                                                 *)
(*      Amount      CoinDec                                                *)
(*      bid         Coin                                                   *)
(*      ask         Coin                                                   *)
(*      exchrate    Dec                                                    *)
(* }                                                                       *)
(***************************************************************************)

OrderType == PendingType \cup MarketType 



(**************************************************************************)
(* Pair plus Coin Type                                                    *)
(*                                                                        *)
(* Each pair is a set with two coins.  Each pair may have variables that  *)
(* depend on both the pair (set of two coins) as well as one of the coins *)
(* associated with that particular pair                                   *)
(**************************************************************************)
PairPlusCoin == { <<pair, coin>> \in Pair \X Coin: coin \in pair} 

TypeInvariant == 
    /\  orderQ \in [Pair -> Seq(Order)]
    /\  drops \in [Pair -> Nat]
    /\  books \in [PairPlusCoin -> Seq(PositionType)]]
    \* Alternative Declaration
    \* [Pair \X Coin -> Sequences]
    /\  bonds \in [PairPlusCoin -> Nat]]
    
(************************** Variable Initialization ************************)       
        
MarketInit ==  
    /\ orderQ = [p \in Pair |-> <<>>]
    /\ drops \in [Pair |-> Nat]
    \* order books bid sequences
    /\ books = [ppc \in PairPlusCoin |-> <<>>]
    \* liquidity balances for each pair
    /\ bonds = [ppc \in PairPlusCoin |-> NoVal]
    
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
(* bondBid(initial) ^ 2 * erate(final) ^ 2 / (bondAsk(initial)             *)
(***************************************************************************)
MaxBondBid(bookAsk, bondAsk, bondBid) ==  
    LET 
        erateFinal == Head(bookAsk).exchrate
    IN 
        \* MaxBondBid = 
        \* bondAsk(initial) - 
        \* bondBid(initial)^2 * erate(final) ^ 2 / 
        \* erate(initial)
        bondAsk - bondBid^2 * erateFinal^2 \div bondAsk

(******************************* Reconcile *********************************)
(* Iteratively reconcile books records with bonds amounts                  *)
(*                                                                         *)
(* Bond amounts are balanced with the ask and bid books such               *)
(* that effective price of bonded liquidity is within the ask              *)
(* bid bookspread                                                          *)
(***************************************************************************)
\* Need to fix some of the state updates such that existing state is not
\* attempted to be mutated outside of prime definitions
Reconcile(bondAsk, bondBid, bookAsk, bookBid) == 
        \* Internal state update variables
        LET bondAskUpdate == bondAsk
            bondBidUpdate == bondBid
            bookAskUpdate == bookAsk
            bookBidUpdate == bookBid
        IN

        (********************** Iteration **************************)
        (* Iterate over the bookAsk sequence processing bond       *)
        (* purchases until bookAsk record with exchrate less than  *) 
        (* the bond price is reached                               *)
        (***********************************************************)
        LET F[i \in 0 .. Len(bookAsk)] == \* 1st LET

            (*********************** Case 1 ************************)                         
            (* The order at the Head of bookAsk sequence has an    *)
            (* exchange rate (bid/ask) greater than or equal to the*)
            (* ask bond exchange rate (bid bal/ask Val).           *)
            (*******************************************************)
            CASE  GTE(bookAsk(i).exchrate, <<bondAsk, bondBid>>) ->
                    LET maxBondBid == MaxBondBid(
                            bookAskUpdate, 
                            bondAskUpdate, 
                            bondBidupdate
                        )
                    IN  CASE Head(bookAskUpdate).amount >= maxBondBid ->
                            \* Ask Bond pays for the Ask Book order
                            /\ bondAskUpdate == bondAsk - maxBondBid
                
                            \* Bid Bond receives the payment from the Ask Book
                            /\ bondBidUpdate == bondBid + maxBondBid

                            /\  bookAskUpdate == Append(
                                    [
                                        amount: Head(bookAskUpdate).amount - maxBondBid,
                                        exchrate: Head(bookAskUpdate).amount
                                    ], 
                                    Tail(bookAskUpdate)
                                )
                            \* Do not loop back. Move onto other side of AMM
                            \* bondBid maxxed out 
                            
                        \* Order amount is under the AMM bidBond may spend
                        \* at exchrate
                        [] Head(bookAskUpdate).amount < maxBondBid
                            \* Ask Bond pays for the Ask Book order
                            /\ bondAskUpdate == bondAskUpdate - maxBondBid
                
                            \* Bid Bond receives the payment from the Ask Book
                            /\ bondBidUpdate == bondBidUpdate + maxBondBid
                
                            \* The ask book order is removed from the head 
                            /\ bookAskUpdate == Tail(bookAsk)

                            \* Loop back. bondBid AMM has more to spend
                            /\  F[Len(bookAskUpdate)]
                            
                
            (*********************** Case 2 ************************)
            (* Head of bookAsk exchange rate less than ask bond    *)
            (* exchange rate                                       *)
            (*******************************************************)
            []  LT(
                        bookAsk(i).exchrate, 
                        (<<bondAskUpdate, bondBidUpdate>>
                    ) ->
                
                (******************** Iteration ********************)
                (* Iterate over the bookBid sequence processing    *)
                (* purchases until bookBid record with exchrate    *) 
                (* the bond price is reached                       *)
                (***************************************************)
                LET G[j \in 0 .. Len(bookBidUpdate)] == \* 2nd LET
                
                (***************************************************)
                (*            Case 2.1                             *)                         
                (* Head of bookBid exchange rate                   *)
                (* greater than or equal to the                    *)
                (* updated bid bond exchange rate                  *)
                (***************************************************)
                CASE  LTE(
                        bookBid(j).exchrate, 
                        <<bondBidUpdate, bondAskUpdate>>
                    ) ->
                    \* Find maxBondBid is the Ask direction
                    LET maxBondBid == MaxBondBid(
                            bookBidUpdate, 
                            bondBidUpdate, 
                            bondAskupdate
                        )
                        erate == Head(bookBidUpdate).exchrate
                    IN
                        CASE Head(bookBidUpdate).amount >= maxBondBid ->
                            \* Bid Bond pays for the Bid Book order
                            /\ bondBidUpdate == bondBid - maxBondBid
                
                            \* Ask Bond receives the payment from the Bid Book
                            /\ bondAskUpdate == 
                                bondAskUpdate + 
                                maxBondBid * 
                                erate

                            /\  bookBidUpdate == Append(
                                    [
                                        amount: Head(bookBidUpdate).amount - maxBondBid,
                                        exchrate: erate
                                    ], 
                                    Tail(bookBidUpdate)
                                )
                            \* Loop back to check if AMM has enabled AskBook Order
                            /\  F[len(bookAskUpdate)]
                        \* Order amount is under the AMM bidAsk may spend
                        \* at erate
                        [] Head(bookAskUpdate).amount < maxBondBid ->
                            \* Ask Bond pays for the Bid Book order
                            /\ bondBidUpdate == bondBidUpdate - maxBondBid
                
                            \* Ask Bond receives the payment from the Bid Book
                            /\ bondAskUpdate == bondAskUpdate + maxBondBid * erate 
                
                            \* The ask book order is removed from the head 
                            /\ bookAskUpdate == Tail(bookAsk)
                            
                            \* Loop back as Bid Bond has more it can spend at erate
                            /\ G[Len(Tail(bookBidUpdate))]
                
                (**************************************************)
                (*            Case 2.2                            *)                         
                (* Head of bookBid exchange rate                  *)
                (* less than the updated bid bond                 *)
                (* exchange rate                                  *)
                (*                                                *)
                (* Processing Complete                            *)
                (* Update bonds and books states                  *)
                (**************************************************)
                []  LT(
                            bookBidUpdate(j), 
                            <<bondBidUpdate, bondAskUpdate>>
                        ) ->
                    /\ << bondAskUpdate, bondBidUpdate, bookAskUpdate, bookBidUpdate >> 
            IN G[Len(bookBidUpdate)]
        IN F[Len(bookAskUpdate)]

(***************************** Step Functions ****************************)

\* Optional syntax
(* LET all_limit_orders == Add your stuff in here *)
(* IN {x \in all_limit_orders: x.bid # x.ask} *)
SubmitOrder == 
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
                       
   
ProcessOrder(pair) ==
    \* may be able to just add the book order to the book sequence and then
    \* reconcile, versus handling 1st step in ProcessOrder

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
            bookAsk == books[pair][o.ask]
            bookBid == books[pair][o.bid]
            
            (*************************** Bonds *****************************)
            bondAsk == bonds[pair][o.ask]
            bondBid == bonds[pair][o.bid]
            
            (*************************** Order *****************************)
            orderAmt == o.amount
            
            (*********************** AMM Allowance *************************)
            maxBondBid == MaxBondBid(bondAsk, bondBid, bookAsk, bookBid)  
        IN  
            
            (***************************************************************)
            (* Define Process() to allow for loop back                     *)
            (***************************************************************)
            LET Process == 
        
            (***************************** Stage 1 *************************)
            (* Process the order and update the state of the affected      *)
            (* books or bonds variables                                    *)
            (***************************************************************)
            /\
                    (********************** Case 1.1 ***********************)
                    (*  Book order exchrate greater than or equal to the   *) 
                    (*  head of the bid book                               *)
                    (*******************************************************)
                    CASE  GTE(o.exchrate, Head(bookBid).exchrate) ->
                        /\ books' = [ books EXCEPT ![pair][o.bid] =

                            (**************** Iteration ********************)
                            (* Iterate over the bookBid sequence until bid *)
                            (* book order price of element selected in     *)
                            (* bookBid is greater than order exchrate      *)
                            (*                                             *)
                            (* Then insert the active order before the     *)
                            (* first book order whose exchrate is greater  *)
                            (* than the active order                       *)
                            (***********************************************)
                            LET F[i \in 0 .. Len(bookBid)] == \* 1st LET
                                IF  i = 0 
                                THEN bookBid 
                                ELSE
                                    LET 
                                        topBid == bookBid[i].exchrate
                                        orderBid == o.exchrate
                                    IN
                                        IF  
                                            orderBid < topBid
                                        THEN    
                                            bookBid = InsertAt(
                                                bookBid, 
                                                i, 
                                                [
                                                    amount: orderAmt, 
                                                    exchrate: o.exchrate
                                                ]
                                            )
                                        ELSE
                                            F[i-1]
                            IN  F[Len(bookBid)]]
                        
                    
                    (********************** Case 1.2 ***********************)
                    (* Book order exchrate less than head of bid book      *)
                    (* exchange rate                                       *)
                    (*******************************************************)
                    []  LT(o.exchrate, Head(bookBid).exchrate)

                            (***********************************************)    
                            (* Add book order to head of bid book          *)
                            (***********************************************)
                            /\  bookBid = Append(
                                                [
                                                    amount: orderAmt, 
                                                    exchrate: o.exchrate
                                                ],
                                                bookBid
                                            )

            (************************** Stage 2 ****************************)
            (* Iteratively reconcile books records with bonds amounts      *)
            (*                                                             *)
            (* Bond amounts are balanced with the ask and bid books such   *)
            (* that effective price of bonded liquidity is within the ask  *) 
            (* bid bookspread                                              *)
            (***************************************************************)   
            /\  LET  
                    pairUpdate == Reconcile(bondAsk, bondBid, bookAsk, bookBid)
                /\  books' = [
                        books EXCEPT    
                            ![pair][o.ask] = pairUpdate[0]
                            ![pair][o.bid] = pairUpdate[1]
                    ]
                /\  bonds' = [
                        bonds EXCEPT
                            ![pair][o.ask] = pairUpdate[2]
                            ![pair][o.bid] = pairUpdate[3]
                    ]
    IN Process(pair)
                
Next == \/ \E p: p == {c, d} \in Pair : c != d :    \/ ProcessPair(p)
                                                    \/ Provision(p)
                                                    \/ Liquidate(p)
        \/ SubmitOrder

=============================================================================
\* Modification History
\* Last modified Tue May 11 20:37:01 CDT 2021 by cdusek
\* Last modified Tue Apr 20 22:17:38 CDT 2021 by djedi
\* Last modified Tue Apr 20 14:11:16 CDT 2021 by charlesd
\* Created Tue Apr 20 13:18:05 CDT 2021 by charlesd
