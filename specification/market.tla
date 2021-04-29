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
         /\ bids = [p \in PAIR |-> c \in p |-> <<>>]
         \* liquidity balances for each pair
         /\ bonds = [p \in PAIR |-> c \in p |-> NoVal]
         

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
    
        \* Is o a book order?
        \* Check to see if record has exchrate
        \/  /\ o.exchrate != {}
            
            \* Stage 1
            \* Reconcile with bid book queue
            LET lowBid = Head(bids[pair][o.bid]).exchrate
            IN  
                \* Is book order exchrate greater than
                \* the head of the bid book?
                \/  /\ lowBid > o.exchrate
                
                \* Is book order exchrate equal to head
                \* of the bid book?
                \/  lowBid = o.exchrate
                
            \* Stage 2
            \* Reconcile o with ask book if exchrate
            \* is less than the head of bid book.
                
                \* Is ask book for pair not empty?
                \/ /\ bids[pair][o.ask] != <<>>
                    /\
                    
                \* Well, Is ask book for pair empty?
                \/ /\ bids[pair][o.ask] = <<>>
        
        \* Is o a bond order?
        \* Order has empty exchrate field
        \/  /\ o.exchrate = {}
            /\  LET bondAsk == bonds[pair][o.ask]
                    bondBid == bonds[pair][o.bid]
                IN  
                    \* Let askAmount be the amount of ask coin
                    \* corresponding to the amount of bid coin
                    LET askAmount == BondAskAmount(bondAsk, bondBid, o.amount) 
                    IN  \* Is there enough liquidity on ask bond?  
                        /\ askAmount < bondAsk
                        \* Reconcile Bonds with Books
                        /\  LET (*******************************************)
                                (* bookAsk: The sequence of book entries   *)
                                (* where the user has deposited the        *)
                                (* "bid coin" in return for the for the    *) 
                                (* "ask coin" at a given exchange rate     *)
                                (*******************************************)
                                bookAsk = books[pair][o.ask]
                                
                                (*******************************************)
                                (* bookBid is the sequence of book entries *)
                                (* where the user has deposited the        *)
                                (* "ask coin in return for the for the     *)
                                (* "bid coin" at a given exchange rate     *)
                                (*******************************************)
                                bookBid = books[pair][o.bid]
                                
                                (*******************************************)
                                (* bookAskUpd: The initial update to       *)
                                (* bond "ask coin" balance                 *)
                                (*******************************************)
                                bondAskUpd = bondAsk - askAmount

                                (*******************************************)
                                (* bookBidUpd: The initial update to       *)
                                (* bond "bid coin" balance                 *)
                                (*******************************************)
                                bondBidUpd = bondBid + o.amount
                            IN  \* For each book entry in ask book 
                                LET F[i \in 0 .. Len(bookAsk)] == \* 1st LET
                                    (***************************************)
                                    (*              Case 1                 *)                         
                                    (* Head of bookAsk exchange rate       *)
                                    (* greater than or equal to the        *)
                                    (* updated bond exchange rate          *)
                                    (***************************************)
                                    \/  /\ bookAsk(i).exchrate >= (bondAskUpd \div bondBidUpd)
                                        /\ bondBidUpd = bondBidUpd - bookAsk(i).amount
                                        /\ bondAskUpd = bondAskUpd - bookAsk(i).amount
                                        /\ bookAsk = Tail(bookAsk)
                                        /\ F[Len(bookAsk)]
                                        \* For each book entry in the bid book
                                    (***************************************)
                                    (*              Case 2                 *)                         
                                    (* Head of bookAsk exchange rate       *)
                                    (* less than the updated bond          *)
                                    (* exchange rate                       *)
                                    (***************************************)
                                    \/  /\ bookAsk(i).exchrate > (bondAskUpd \div bondBidUpd)
                                        LET G[j \in 0 .. Len(bookBid)] == \* 2nd LET
                                        \/ bookAsk(i).exchrate > (bondAskUpd \div bondBidUpd)
                                            /\
                                        \/  /\  bonds' = [bonds EXCEPT bondBid = 
                                            /\  bids' = [bids EXCEPT ![pair][bidCoin]] 
                                    \/  /\  bonds' = 
                                        /\  bids'
                                    IN G[Len(bookBid)]
                                IN F[Len(bookAsk)]
                    

                        /\ bonds' = 
                            [
                             bonds EXCEPT ![pair][o.ask] = @ - bondAsk
                                          ![pair][o.bid] = @ + bondBid
                            ]
                        /\ orders' = [orders EXCEPT ![pair][o.ask] = ]
 
                  



=============================================================================
\* Modification History
\* Last modified Tue Apr 20 22:17:38 CDT 2021 by djedi
\* Last modified Tue Apr 20 14:11:16 CDT 2021 by charlesd
\* Created Tue Apr 20 13:18:05 CDT 2021 by charlesd
