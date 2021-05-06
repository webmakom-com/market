------------------------------- MODULE market -------------------------------
EXTENDS     Naturals, Sequences

CONSTANT    COIN,   \* Set of all coins
            PAIR   \* Set of all pairs of coins
           
VARIABLE    book,   \* Order Book
            bonds,  \* AMM Bond Curves

-----------------------------------------------------------------------------
NoVal ==    CHOOSE v : v \notin Nat

PAIR == {{c \in COIN, d \in COIN}: c != d}

Type ==

Book == [amount: Nat, bid: COIN, ask: COIN, exchrate: <Nat, Nat>]

Bond == [amount: Nat, bid: COIN, ask: COIN]

Order == Book \cup Bond

Pool == { <{c, Nat}, {d, Nat}> : c \in COIN, d \in COIN \ c }

Type == /\  orderQ \in [PAIR -> Seq(Order)]
        /\  books \in [PAIR -> COIN -> Seq(Nat X Nat)]
        /\  bonds \in [PAIR -> COIN -> Nat]    
         

Init ==  /\ orderQ = [p \in PAIR |-> <<>>]
         \* order books bid sequences
         /\ books = [p \in PAIR |-> c \in p |-> <<>>]
         \* liquidity balances for each pair
         /\ bonds = [p \in PAIR |-> c \in p |-> NoVal]

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
    /\ \E o \in Order :
        /\ orderQ’ = [orderQ EXCEPT ![{o.bid, o.ask}] = Append(@, o)
        /\ UNCHANGED liquidity

BondAskAmount(bondAskBal, bondBidBal, bidAmount) ==
    (bondAskBal * bidAmount) \div bondBidBal
   
ProcessOrder(pair) =

    (*************************** Enabling Condition ************************)
    (* Order queue is not empty                                            *)
    (***********************************************************************)
    /\ orderQ[pair] != <<>>
    
    (*************************** Internal Variables ************************)
    (* Internal variables are used to track intermediate changes to books  *)
    (* bonds on copy of the working state                                  *)
    (***********************************************************************)
    /\ LET o = Head(orderQ[pair]) IN
        LET (*************************** Books *****************************)
            bookAsk == books[pair][o.ask]
            bookBid == books[pair][o.bid]
            
            (*************************** Bonds *****************************)
            bondAsk == bonds[pair][o.ask]
            bondBid == bonds[pair][o.bid]
            
            (*************************** Order *****************************)
            orderAmt == o.amount
            
            (***************************************************************)
            (* Max Bid that Bond liquidity can handle without effecting    *)
            (* book orders                                                 *)
            (*                                                             *)
            (* Expression origin:                                          *)
            (* (bondAsk - x * k_bidBook) / (bondBid + x) = k_bidBook       *)
            (* k == exchrate or ask_coin/bid_coin                          *)
            (*                                                             *)
            (* Solve for x:                                                *)
            (* x = (bondAsk/k_book - bondBid)/2                            *)
            (***************************************************************)
            maxBondBid ==  (bondAsk/Head(
                    books[pair][o.bid]).exchrate
                ) - bondBid) / 2
        IN 
            LET Process == 
        
            (***************************** Stage 1 *************************)
            (* Process the order and update the state of the affected       )
            (* books or bonds variables                                     )
            (***************************************************************)
            /\
            
                (************************** Case 1 *************************)
                (* Order is a Book / Limit Order                           *)
                (* Order is a Book / Limit Order if the record has exchrate*)
                (* limit.                                                  *)
                (***********************************************************)    
                \/  /\ o.exchrate != {}
                    
                    (********************** Case 1.1 ***********************)
                    (*  Book order exchrate greater than or equal to the   *) 
                    (*  head of the bid book                               *)
                    (*******************************************************)
                    \/  /\ o.exchrate >= Head(bookBid).exchrate
                        /\ books’ [books EXCEPT ![pair][o.bid] = 
                            LET F[i \in 0 .. Len(bookBid)] == \* 1st LET
                                IF  i = 0 THEN bookBid ELSE
                                \/  /\  o.ecxchrate < bookBid(i).exchrate
                                    /\  bookBid == InsertAt(
                                            bookBid, 
                                            i, 
                                            [
                                                amount: orderAmt, 
                                                exchrate: o.exchrate
                                            ]
                                        )
                                \/  /\  o.exchrate <= bookBid
                                    /\  F[i-1]
                            IN  F[Len(bookBid)]
                    
                    (********************** Case 1.2 ***********************)
                    (*  Book order exchrate less than head of bid          *)
                    (*  book                                               *)
                    (*******************************************************)
                    \/  /\ o.exchrate < Head(bookBid).exchrate

                        (***************** Case 1.2.1 **********************)
                        (* Book bid price greater than bond price          *)
                        (*  Review how the less than or equal to would     *)
                        (** change behavior                                *)
                        (***************************************************)
                        \/  /\  (bondAsk * orderAmt) / bondBid > 
                                orderAmt * o.exchrate
                            
                            (*************** Case 1.2.1.1 ******************)
                            (* Order amount is less than or equal to the   *) 
                            (* moxBondBid                                *)
                            (***********************************************)
                            \/  orderAmt <= moxBondBid
                                /\  bondAsk == bondAsk - BondAskAmount(
                                        bondAsk,
                                        bondBid,
                                        orderAmt
                                    )
                                /\  bondBid == bondBid + orderAmt

                            (*************** Case 1.2.1.2 ******************)
                            (* Order amount is above the amount of         *)
                            (* the moxBondBid                            *) 
                            (***********************************************)
                            \/  orderAmt > moxBondBid
                                \* Then settle the moxBondBid
                                \* and loop back
                                /\  bondAsk == bondAsk - BondAskAmount(
                                        bondAsk, 
                                        bondBid, 
                                        moxBondBid
                                    )
                                /\  bondBid == bondBid + 
                                /\  orderAmt == orderAmt - moxBondBid
                                /\  bookBid == Append(
                                        [
                                            amount: orderAmt, 
                                            exchrate: o.exchrate
                                        ]
                                    )
                                /\  Process()
                
                (************************ Case 2 **************************)
                (* Order is a Bond / AMM Order                            *)
                (* Order is a Bond / AMM Order if the record does not have*)
                (* a value in the exchrate field                          *)
                (**********************************************************)
                \/  /\ o.exchrate = {}
                            (*************** Case 1.2.1.1 ******************)
                            (* Order amount is less than or equal to the   *) 
                            (* moxBondBid                                *)
                            (***********************************************)
                            \/  orderAmt <= moxBondBid
                                /\  bondAsk == bondAsk - orderAmt
                                /\  bondBid == bondBid + orderAmt

                            (*************** Case 1.2.1.2 ******************)
                            (* Order amount is above the amount of         *)
                            (* the moxBondBid                            *) 
                            (***********************************************)
                            \/  orderAmt > moxBondBid
                                \* Then settle the moxBondBid
                                \* and loop back
                                /\  bondAsk == bondAsk - BondAskAmount(
                                        bondAsk, 
                                        bondBid, 
                                        moxBondBid
                                    )
                                /\  bondBid == bondBid + moxBondBid
                                /\  orderAmt == orderAmt - moxBondBid
                                /\  'books = [books EXCEPT ![pair][bid] = 
                                    Append(
                                    [amount: orderAmt, exchrate: o.exchrate]
                                )]
                        \* Is there enough liquidity on ask bond?  
                        (********************* Case 2.1 *******************)
                        (* Order is a bond order                          *)
                        (* Order has empty exchrate field                 *)
                        (**************************************************)
                            \* Does bond have enough liquidity to handle entire order?
                            \/  orderAmt <= moxBondBid
                                /\  bondAsk == bondAsk - BondAskAmount(
                                        bondAsk, 
                                        bondBid, 
                                        orderAmt
                                    )
                                /\  bondBid == bondBid + orderAmt
                                  
                                (*******************************************)
                                (* bookAskUpd: The initial update to       *)
                                (* bond "ask coin" balance                 *)
                                (*******************************************)
                                /\  bondAsk == bondAsk - askAmount
                                (*******************************************)
                                (* bookBidUpd: The initial update to       *)
                                (* bond "bid coin" balance                 *)
                                (*******************************************)
                                /\  bondBid == bondBid + o.amount
            (***************************** Stage 2 *************************)
            (* Iteratively reconcile books records with bonds amounts      *)
            (*                                                             *)
            (* Bond amounts are balanced with the ask and bid books such   *)
            (* that effective price of bonded liquidity is within the ask  *) 
            (* bid bookspread                                              *)
            (***************************************************************)   
                \* Reconcile Bonds with Books
            /\  \* For each book entry in ask book 
                LET F[i \in 0 .. Len(bookAsk)] == \* 1st LET
                    (***************************************)
                    (*              Case 1                 *)                         
                    (* Head of bookAsk exchange rate       *)
                    (* greater than or equal to the        *)
                    (* updated bond exchange rate          *)
                    (***************************************)
                    \/  /\ bookAsk(i).exchrate >= (bondAskUpd \div bondBidUpd)
                        \* Ask Bond pays for the ask book order
                        /\ bondAskUpd == bondAskUpd - bookAsk(i).amount
                        \* Bid Bond receives the payment from the ask book
                        /\ bondBidUpd == bondBidUpd + bookAsk(i).amount
                        \* The ask book order is removed from the head 
                        /\ bookAsk == Tail(bookAsk)
                        \* Loop back
                        /\ F[Len(bookAsk)]
                        
                    (***************************************)
                    (*              Case 2                 *)                         
                    (* Head of bookAsk exchange rate       *)
                    (* less than the updated bond          *)
                    (* exchange rate                       *)
                    (***************************************)
                    \/  /\ bookAsk(i).exchrate < (bondAskUpd \div bondBidUpd)
                        LET G[j \in 0 .. Len(bookBid)] == \* 2nd LET
                        (***************************************)
                        (*            Case 2.1                 *)                         
                        (* Head of bookBid exchange rate       *)
                        (* greater than or equal to the        *)
                        (* updated bid bond exchange rate      *)
                        (***************************************)
                        \/ bookBid(i).exchrate >= (bondBidUpd \div bondAskUpd)
                            \* Bid Bond pays for the bid book order
                            /\ bondBidUpd = bondBidUpd - bookBid(i).amount
                            \* Ask Bond receives the payment from the ask book
                            /\ bondAskUpd = bondAskUpd + bookBid(i).amount
                            \* The Bid Book order is removed from the head 
                            /\ bookBid = Tail(bookBid)
                            \* Loop back
                            /\ F[Len(bookAsk)]
                        (***************************************)
                        (*            Case 2.2                 *)                         
                        (* Head of bookBid exchange rate       *)
                        (* less than the updated bid bond      *)
                        (* exchange rate                       *)
                        (*                                     *)
                        (* Processing Complete                 *)
                        (* Update bonds and books states        *)
                        (***************************************)
                        \/  /\  bonds' = [
                                    bonds EXCEPT    
                                        ![pair][o.bid] = bondBidUpd
                                        ![pair][o.ask] = bondAskUpd
                                ]
                            /\  books' = [
                                    books EXCEPT
                                        ![pair][o.bid] = bookBid
                                        ![pair][o.ask] = bookAsk
                                ]
                    IN G[Len(bookBid)]
                IN F[Len(bookAsk)]
            IN  Process()    

=============================================================================
\* Modification History
\* Last modified Tue Apr 20 22:17:38 CDT 2021 by djedi
\* Last modified Tue Apr 20 14:11:16 CDT 2021 by charlesd
\* Created Tue Apr 20 13:18:05 CDT 2021 by charlesd
