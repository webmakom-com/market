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

Init ==  /\ orderQ = [p \in PAIR |-> <<>>]
         \* order books bid sequences
         /\ books = [p \in PAIR |-> c \in p |-> <<>>]
         \* liquidity balances for each pair
         /\ bonds = [p \in PAIR |-> c \in p |-> NoVal]

InsertAt(s, i, e) ==
  (**************************************************************************)
  (* Inserts element e at the position i moving the original element to i+1 *)
  (* and so on.  In other words, a sequence t s.t.:                         *)
  (*   /\ Len(t) = Len(s) + 1                                               *)
  (*   /\ t[i] = e                                                          *)
  (*   /\ \A j \in 1..(i - 1): t[j] = s[j]                                  *)
  (*   /\ \A k \in (i + 1)..Len(s): t[k + 1] = s[k]                         *)
  (**************************************************************************)
  SubSeq(s, 1, i-1) \o <<e>> \o SubSeq(s, i, Len(s))
         

SubmitOrder == 
    /\ \E o \in Order :
        /\ orderQ’ = [orderQ EXCEPT ![{o.bid, o.ask}] = Append(@, o)
        /\ UNCHANGED liquidity

BondAskAmount(bondAskBal, bondBidBal, bidAmount) ==
    (bondAskBal * bidAmount) \div bondBidBal
   
ProcessOrder(pair) =    
    \* Are there orders to process for this pair of coins?
    /\ orderQ[pair] != <<>>
    /\ LET o = Head(orderQ[pair]) IN
        LET bookAsk == books[pair][o.ask]
            bookBid == books[pair][o.bid]
            bondAsk == bonds[pair][o.ask]
            bondBid == bonds[pair][o.bid]
            orderAmt == o.amount
            maxBondOrder == (bondAsk - askBid.exchrate * bondBid) /
                            (1 + askBid.exchrate)
        IN  \* Case 1
            \* Book Order
            \* Check to see if record has exchrate
            /\  \/  /\ o.exchrate != {}
                    
                    \*  Case 1.1
                    \*  Book order exchrate greater than head
                    \*  of the bid book?
                    \/  /\ Head(bookBid).exchrate < o.exchrate
                        /\ books’ [books EXCEPT ![pair][o.bid] = 
                            LET F[i \in 0 .. Len(bookBid)] == \* 1st LET
                            \/ bookBid(i).exchrate > o.exchrate
                                /\ bookBid == InsertAt(
                                    bookBid, 
                                    i, 
                                    [amount: orderAmt, exchrate: o.exchrate]
                                )
                            \/ bookBid >= o.exchrate
                                /\ F
                    
                    \*  Case 1.2
                    \*  Book order exchrate equal to head
                    \/  /\ Head(bookBid).exchrate  = o.exchrate
                            \* Case 1.2.1
                            \/ Head(bookBid).amount > orderAmt
                            \* Case 1.2.2
                            \/ Head(bookBid).amount = orderAmt
                            \* Case 1.2.3
                            \/ Head(bookBid).amount < orderAmt
                    
                    \*  Case 1.3
                    \/  /\ Head(bookBid).exchrate > o.exchrate
                        \* Case 1.3.1
                        \* Book bid price greater than bond price
                        \* *** Review how the less than or equal to would change
                        \* behavior ***
                        \/  /\  (bondAsk * orderAmt) / bondBid > orderAmt * o.exchrate
                            \* Does bond have enough liquidity to handle entire order?
                            \/  orderAmt <= maxBondOrder
                                /\  bondAsk == bondAsk - orderAmt
                                /\  bondBid == bondBid + orderAmt
                            \* Is order amount above the amount of liquidity
                            \* available before hitting bookOrder?
                            \/  orderAmt > maxBondOrder
                                \* Then settle the maxBondOrder
                                \* and loop back
                                /\  bondAsk == bondAsk - maxBondOrder
                                /\  bondBid == bondBid + maxBondOrder
                                /\  orderAmt == orderAmt - maxBondOrder
                                /\  'books = [books EXCEPT ![pair][bid] = 
                                    Append(
                                    [amount: orderAmt, exchrate: o.exchrate]
                                )]
                        
                            
                        \* Stage 2
                        \* Reconcile o with ask book if exchrate
                        \* is less than the head of bid book.
                            
                            \* Is ask book for pair not empty?
                            \/  /\ books[pair][o.ask] != <<>>
                                /\
                                
                            \* Well, Is ask book for pair empty?
                            \/  /\ books[pair][o.ask] = <<>>
                
                \* Case 2
                \* Is o a bond order?
                \* Order has empty exchrate field
                \/  /\ o.exchrate = {}
                        \* Let askAmount be the amount of ask coin
                        \* corresponding to the amount of bid coin
                        LET askAmount == BondAskAmount(bondAsk, bondBid, o.amount) 
                        IN  \* Is there enough liquidity on ask bond?  
                            /\ askAmount < bondAsk
                            /\  (*******************************************)
                                (* bookAskUpd: The initial update to       *)
                                (* bond "ask coin" balance                 *)
                                (*******************************************)
                                bondAsk == bondAsk - askAmount
                            /\  (*******************************************)
                                (* bookBidUpd: The initial update to       *)
                                (* bond "bid coin" balance                 *)
                                (*******************************************)
                                bondBid == bondBid + o.amount
                
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

=============================================================================
\* Modification History
\* Last modified Tue Apr 20 22:17:38 CDT 2021 by djedi
\* Last modified Tue Apr 20 14:11:16 CDT 2021 by charlesd
\* Created Tue Apr 20 13:18:05 CDT 2021 by charlesd
