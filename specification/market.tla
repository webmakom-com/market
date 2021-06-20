------------------------------- MODULE market -------------------------------
EXTENDS     Naturals, Sequences, SequencesExt

CONSTANT    Coin,       \* Set of all coins
            Denom,      \* Set of all denoms
            Denominator,\* Set of all possible denominators
            Input,      \* Set of all possible input amounts
            NOM,        \* NOM coin. Single Constant Collateral.
            Expiration  \* Set of all expirations
           
VARIABLE    books,      \* Order Book
            bonds,      \* AMM Bond Curves
            orderQ, 
            drops

ASSUME Denom \subseteq Coin
ASSUME Denominator \in Nat
-----------------------------------------------------------------------------
(***************************** Type Declarations ***************************)

NoVal == CHOOSE v : v \notin Nat

\* All exchange rates are represented as numerator/denominator tuples
ExchRateType == {<<a, b>> : a \in Nat, b \in Denominator}

\* Pairs of coins are represented as couple sets
\* { {{a, b}: b \in Coin \ {a}}: b \in Coin} 
PairType == {{a, b}: a \in Coin, b \in Coin \ {a}}

(******************************* Limit Order *******************************)
(* The Limit Order is an exchange order that defines an upper limit to the *)
(* strike exchrate defined as ask/bid price.                               *)
(*                                                                         *)
(* Limit Orders are persistent until revoked or fulfilled.  Revoked Limit  *)
(* Orders will return any portion of the bidAmount that did not execute    *)
(* back to user account                                                    *)
(*                                                                         *)
(* bidAmount <Nat>: Amount of Bid Coin                                     *)
(* bid <Coin>: Bid Coin                                                    *)
(* ask <Coin>: Ask Coin                                                    *)
(* exchrate <Real>: Exchange rate (ask/bid) limit                          *)
(***************************************************************************)
LimitType == [
    amount: Nat, 
    bid: Coin, 
    ask: Coin, 
    exchrate: ExchRateType
]

(******************************* Market Order ******************************)
(* The Market Order is an exchange order that does not limit the strike    *)
(* exchrate (ask/bid).  The Market Order pulls the requested amount of ask *)
(* coin liquidity at the minimum cost based on AMM liquidity pool and      *) 
(* the limit order books.                                                  *)
(*                                                                         *)
(* Limit Orders are fulfilled at the time of order.                        *)
(*                                                                         *)
(* bidAmount <Nat>: Amount of Bid Coin                                     *)
(* bid <Coin>: Bid Coin                                                    *)
(* ask <Coin>: Ask Coin                                                    *)
(***************************************************************************)
MarketType == [
    bidAmount: Nat, 
    bid: Coin, 
    ask: Coin
]

OrderType == LimitType \cup MarketType \cup SwapType 

(***************************************************************************)
(* Position Type                                                           *)
(*                                                                         *)
(* The position type is the order book record that is maintained when a    *)
(* limit order has an unfulfilled outstanding amount                       *)
(*                                                                         *)
(* amount <Nat>: Amount of Bid Coin                                        *)
(* exchrate <ExchRateType>: ExchRate Limit (Ask Coin / Bid Coin)           *)
(***************************************************************************)
PositionType == [
    amount: Nat, 
    exchrate: ExchRateType
]

(**************************************************************************)
(* Pair plus Coin Type                                                    *)
(*                                                                        *)
(* Each pair is a set with two coins.  Each pair may have variables that  *)
(* depend on both the pair (set of two coins) as well as one of the coins *)
(* associated with that particular pair                                   *)
(**************************************************************************)
PairPlusCoin == { <<pair, coin>> \in Pair \X Coin: coin \in pair} 

Type == 
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
(* (bondAsk - x * kAskBook) / (bondBid + x) = kAskBook                     *)
(* erate == exchrate or ask_coin/bid_coin                                  *)
(*                                                                         *)
(* Solve for x:                                                            *)
(* x = (bondAsk/erateAskBook - bondBid)/2                                  *)
(***************************************************************************)
MaxBondBid(bookAsk, bondAsk, bondBid) ==  
    LET 
        erateAskHead == Head(bookAsk).exchrate
    IN 
        \* (bondAsk / erateAskHead - bondBid) / 2
        (
            bondAsk \div 
            erateAskHead[1] * 
            erateAskHead[0] - 
            bondBid
        ) \div 2

(******************************* Reconcile *********************************)
(* Iteratively reconcile books records with bonds amounts                  *)
(*                                                                         *)
(* Bond amounts are balanced with the ask and bid books such               *)
(* that effective price of bonded liquidity is within the ask              *)
(* bid bookspread                                                          *)
(***************************************************************************) 
Reconcile(bondAsk, bondBid, bookAsk, bookBid) == 

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
            \* need to constrain this. Right now bond is allowed buy too much
            \/  /\ GTE(bookAsk(i).exchrate, <<bondAsk, bondBid>>)
                
                \* Ask Bond pays for the Ask Book order
                /\ bondAsk == bondAsk - bookAsk(i).amount
                
                \* Bid Bond receives the payment from the Ask Book
                /\ bondBid == bondBid + bookAsk(i).amount
                
                \* The ask book order is removed from the head 
                /\ bookAskUpdate = Tail(bookAsk)
                
                \* Loop back
                /\ F[Len(Tail(bookAsk)]
                
            (*********************** Case 2 ************************)
            (* Head of bookAsk exchange rate less than ask bond    *)
            (* exchange rate                                       *)
            (*******************************************************)
            \/  /\ LT(bookAsk(i).exchrate, (<<bondAsk, bondBid>>)
                
                (******************** Iteration ********************)
                (* Iterate over the bookBid sequence processing    *)
                (* purchases until bookBid record with exchrate    *) 
                (* the bond price is reached                       *)
                (***************************************************)
                LET G[j \in 0 .. Len(bookBid)] == \* 2nd LET
                
                (***************************************************)
                (*            Case 2.1                             *)                         
                (* Head of bookBid exchange rate                   *)
                (* greater than or equal to the                    *)
                (* updated bid bond exchange rate                  *)
                (***************************************************)
                \/ LTE(bookBid(j).exchrate, <<bondBid, bondAsk>>)
                    \* Bid Bond pays for the bid book order
                    /\ bondBid = bondBid - bookBid(j).amount
                    \* Ask Bond receives the payment from the ask book
                    /\ bondAsk = bondAsk + bookBid(j).amount
                    \* The Bid Book order is removed from the head 
                    /\ bookBid = Tail(bookBid)
                    \* Loop back
                    /\ G[Len(Tail(bookBid))]
                
                (**************************************************)
                (*            Case 2.2                            *)                         
                (* Head of bookBid exchange rate                  *)
                (* less than the updated bid bond                 *)
                (* exchange rate                                  *)
                (*                                                *)
                (* Processing Complete                            *)
                (* Update bonds and books states                  *)
                (**************************************************)
                \/  /\ LT(bookBid(j) , <<bondBid, bondAsk>>))
                    /\ << bondAsk, bondBid, bookAsk, bookBid >> 
            IN G[Len(bookBid)]
        IN F[Len(bookAsk)]

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
            
            \* this functions needs to be pulled out and used both here and
            \* in Reconcile.
            (***************************************************************)
            (* Max amount that Bond pool may sell of ask coin without      *)
            (* executing an ask coin book limit order.                     *)
            (*                                                             *)
            (* Expression origin:                                          *)
            (* (bondAsk - x * kAskBook) / (bondBid + x) = kAskBook         *)
            (* erate == exchrate or ask_coin/bid_coin                          *)
            (*                                                             *)
            (* Solve for x:                                                *)
            (* x = (bondAsk/erateAskBook - bondBid)/2                          *)
            (***************************************************************)
            maxBondBid ==  
                LET 
                    erateAskHead == Head(books[pair][o.ask]).exchrate
                IN 
                    \* (bondAsk / erateAskHead - bondBid) / 2
                    (
                        bondAsk \div 
                        erateAskHead[1] * 
                        erateAskHead[0] - 
                        bondBid
                    ) \div 2
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
            
                (************************** Case 1 *************************)
                (* Order is a Book / Limit Order                           *)
                (*                      
                (* Order is a Book / Limit Order if the record has exchrate*)
                (* limit.                                                  *)
                (***********************************************************)    
                \/  /\ o.exchrate # {}
                    
                    (********************** Case 1.1 ***********************)
                    (*  Book order exchrate greater than or equal to the   *) 
                    (*  head of the bid book                               *)
                    (*******************************************************)
                    \/  /\ GTE(o.exchrate, Head(bookBid).exchrate)
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
                    (*  Book order exchrate less than head of bid book     *)
                    (*******************************************************)
                    \/  /\ LT(o.exchrate, Head(bookBid).exchrate)

                            (***********************************************)    
                            (* Find amount of bond allowed to be sold      *)
                            (* before it hits the order exchrate           *)
                            (***********************************************)
                            /\  LET maxBondBid ==
                                    (
                                        bondAsk \div 
                                        o.exchrate[0] * 
                                        o.exchrate[1] - 
                                        bondBid
                                    ) \div 2
                                IN
                                    
                                    (*************** Case 1.2.1 ************)
                                    (* Order amount is less than or equal  *) 
                                    (* to maxBookBid amount                *)
                                    (***************************************)
                                    \/  /\  maxBondBid < orderAmt
                                    
                                        /\  bondAsk = bondAsk - BondAskAmount(
                                                bondAsk,
                                                bondBid,
                                                orderAmt
                                            )
                                            
                                        /\  bondBid = bondBid + orderAmt
    
                                    (*************** Case 1.2.2 ************)
                                    (* Order amount is above the amount of *)
                                    (* the maxBookBid                      *) 
                                    (***************************************)
                                    \/  /\  maxBondBid > orderAmt
                                    
                                        (***********************************)
                                        (* Then settle the maxBookBid      *)
                                        (* amount and place order at exch  *)
                                        (* rate in books                   *)
                                        (***********************************)
                                        /\  bondAsk = bondAsk - BondAskAmount(
                                                bondAsk, 
                                                bondBid, 
                                                maxBondBid
                                            )
                                        /\  bondBid = bondBid + maxBondBid
                                        /\  orderAmt = orderAmt - maxBondBid
                                        /\  bookBid = Append(
                                                [
                                                    amount: orderAmt, 
                                                    exchrate: o.exchrate
                                                ],
                                                bookBid
                                            )
                    
                
                (************************ Case 2 ***************************)
                (* Order is a Bond / AMM Order                             *)
                (* Order is a Bond / AMM Order if the record does not have *)
                (* a value in the exchrate field                           *)
                (***********************************************************)
                \/  /\ o.exchrate = {}

                        (******************* Case 2.1 **********************)
                        (* Order amount is less than or equal to the       *) 
                        (* maxBondBid                                      *)
                        (***************************************************)
                        \/  orderAmt <= maxBondBid
                            /\  bondAsk == bondAsk - BondAskAmount(
                                    bondAsk, 
                                    bondBid, 
                                    orderAmt
                                )
                            /\  bondBid == bondBid + orderAmt

                        (******************* Case 2.2 **********************)
                        (* Order amount is greater than maxBondBid         *)
                        (* the maxBondBid                                  *) 
                        (***************************************************)
                        \/  orderAmt > maxBondBid
                            /\  bondAsk == bondAsk - BondAskAmount(
                                    bondAsk, 
                                    bondBid, 
                                    maxBondBid
                                )
                            /\  bondBid == bondBid + maxBondBid
                            /\  orderAmt == orderAmt - maxBondBid
                            /\  'books = [books EXCEPT ![pair][bid] = 
                                Append(
                                [amount: orderAmt, exchrate: o.exchrate]
                            )]
            (************************** Stage 2 ****************************)
            (* Iteratively reconcile books records with bonds amounts      *)
            (*                                                             *)
            (* Bond amounts are balanced with the ask and bid books such   *)
            (* that effective price of bonded liquidity is within the ask  *) 
            (* bid bookspread                                              *)
            (***************************************************************)   
            \/  LET  
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
