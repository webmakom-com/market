------------------------------- MODULE market -------------------------------
EXTENDS     Naturals, Sequences, SequencesExt, Reals

CONSTANT    Coin,   \* Set of all coins
            Denom,  \* Set of all denoms
            Pair,   \* Set of all pairs of coins
            NOM,    \* NOM coin. Single Constant Collateral.
            Expire  \* Set of all expirations
           
VARIABLE    books,  \* Order Book
            bonds,
            orderQ,   \* AMM Bond Curves
-----------------------------------------------------------------------------
(*************************** Constant Declarations *************************)

NoVal == CHOOSE v : v \notin Real

(* All amounts are Real *)
Amount == r \in Real

(* All exchange rates are Real *)
ExchRate == r \in Real

(* Pairs of coins are represented as couple sets *)
Pair == {c \in Coin, d \in Coin \ c}

(******************************* Limit Order *******************************)
(* The Limit Order is an exchange order that defines an upper limit to the *)
(* strike exchrate defined as ask/bid.                                     *)
(*                                                                         *)
(* Limit Orders are persistent until revoked or fulfilled.  Revoked Limit  *)
(* Orders will return any portion of the bidAmount that did not execute    *)
(* back to user account                                                    *)
(*                                                                         *)
(* bidAmount <Real>: Amount of Bid Coin                                    *)
(* bid <Coin>: Bid Coin                                                    *)
(* ask <Coin>: Ask Coin                                                    *)
(* exchrate <Real>: Exchange rate (ask/bid) limit                          *)
(***************************************************************************)
Limit == [amount: Amount, bid: Coin, ask: Coin, exchrate: ExchRate]

(******************************* Market Order ******************************)
(* The Market Order is an exchange order that does not limit the strike    *)
(* exchrate (ask/bid).  The Market Order pulls the requested amount of ask *)
(* coin liquidity at the minimum cost based on AMM liquidity pool and      *) 
(* the limit order books.                                                  *)
(*                                                                         *)
(* Limit Orders are fulfilled at the time of order.                        *)
(*                                                                         *)
(* bidAmount <Real>: Amount of Bid Coin                                    *)
(* bid <Coin>: Bid Coin                                                    *)
(* ask <Coin>: Ask Coin                                                    *)
(***************************************************************************)
Market == [
    bidAmount: Amount, bid: Coin, ask: Coin]

(***************************************************************************)
(* Swap from one currency to another.                                      *)
(*                                                                         *)
(* Swaps are created by depositing denoms into the Onomy Reserve and are   *)
(* priced by the user that creates them in the denom of their choice.      *)                                                      *)
(*                                                                         *)
(* The creating user must specify an expiration date upon which the denoms *)
(* are returned to the user and the swap is no longer valid.               *)
(*                                                                         *)
(* A Forward may be represented by a Swap with the same ask and bid denom. *)
(***************************************************************************)
Swap == [
            askDenom: Denom, 
            bidDenom: Denom, 
            amountAsk: Real, 
            amountBid: Real,
            \* Expiration set to constant so as to limit number of Swaps
            \* for validation purposes.  Expiration time will not be
            \* limited for implementation
            expiration: Expire,
        ]

Order == Limit \cup Market

Position == [amount: Amount, exchrate: ExchRate]

Type == 
    /\  orderQ \in [Pair -> Seq(Order)]
    /\  books \in [Pair -> [Coin -> Seq(Position)]]
    /\  bonds \in [Pair -> [Coin -> Amount]]
    /\  tokens \in [Pair -> Amount]   
        

MarketInit ==  
    /\ orderQ = [p \in Pair |-> <<>>]
    \* order books bid sequences
    /\ books = [p \in Pair |-> [c \in p |-> <<>>]]
    \* liquidity balances for each pair
    /\ bonds = [p \in Pair |-> [c \in p |-> NoVal]]
    /\ swaps = [u \in User |-> {Swap}]
    
(***************************** Helper Functions ****************************)

InsertAt(s, i, e) ==
  (*************************************************************************)
  (* Inserts element e at the position i moving the original element to    *)
  (* i+1 and so on.  In other words, a sequence t s.t.:                    *)
  (*   /\ Len(t) = Len(s) + 1                                              *)
  (*   /\ t[i] = e                                                         *)
  (*   /\ \A j \in 1..(i - 1): t[j] = s[j]                                 *)
  (*   /\ \A k \in (i + 1)..Len(s): t[k + 1] = s[k]                        *)
  (*************************************************************************)
  SubSeq(s, 1, i-1) \o <<e>> \o SubSeq(s, i, Len(s))
         

SubmitOrder == 
    /\  \E o \in Order : 
        /\  o.bid # o.ask
        /\  orderQ' = [orderQ EXCEPT ![{o.bid, o.ask}] = Append(@, o)]
    /\  UNCHANGED <<books, bonds>>

BondAskAmount(bondAskBal, bondBidBal, bidAmount) ==
    (bondAskBal * bidAmount) \div bondBidBal

Stronger(pair)    ==  CHOOSE c \in pair :  bond[c] <= bond[pair / c]

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
            (* exchange rate greater than or equal to the ask bond *)
            (* exchange rate                                       *)
            (*******************************************************)
            \/  /\ bookAsk(i).exchrate >= (bondAsk \div bondBid)
                
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
            \/  /\ bookAsk(i).exchrate < (bondAsk \div bondBid)
                
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
                \/ bookBid(j).exchrate >= (bondBid \div bondAsk)
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
                \/  /\ bookBid(j) < (bondBid \div bondAsk) 
                    /\ << bondAsk, bondBid, bookAsk, bookBid >> 
            IN G[Len(bookBid)]
        IN F[Len(bookAsk)]

(***************************** Step Functions ****************************)

Provision(pair) ==  \E r \in Real : 
                        LET bond == bonds[pair]
                        IN
                            LET c == Weaker(pair)
                                d == pair \ c
                            IN
                                /\  bonds' = [ bonds EXCEPT 
                                        ![pair][d] = 
                                          @ + @ * (r / bonds[pair][c]),
                                        ![pair][c] = @ + r
                                    ]
                                /\ tokens' = [ tokens EXCEPT 
                                    ![pair] = @ + r ]
                                /\ UNCHANGED << books, orderQ >>

Liquidate(pair) ==  \E r \in Real : 
                        /\  r < tokens[pair]
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
                                    
                                    /\ tokens' = [ tokens EXCEPT 
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
            
            (***************************************************************)
            (* Max amount that Bond pool may sell of ask coin without      *)
            (* executing an ask coin book limit order.                     *)
            (*                                                             *)
            (* Expression origin:                                          *)
            (* (bondAsk - x * kAskBook) / (bondBid + x) = kAskBook         *)
            (* k == exchrate or ask_coin/bid_coin                          *)
            (*                                                             *)
            (* Solve for x:                                                *)
            (* x = (bondAsk/kAskBook - bondBid)/2                          *)
            (***************************************************************)
            maxBondBid ==  
                LET 
                    kAskHead == Head(books[pair][o.ask]).exchrate
                IN 
                    (bondAsk/kAskHead - bondBid) / 2
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
                    \/  /\ o.exchrate >= Head(bookBid).exchrate
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
                    \/  /\ o.exchrate < Head(bookBid).exchrate

                            (***********************************************)    
                            (* Find amount of bond allowed to be sold      *)
                            (* before it hits the order exchrate           *)
                            (***********************************************)
                            /\  LET maxBondBid ==
                                    (bondAsk/o.exchrate - bondBid) / 2
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
