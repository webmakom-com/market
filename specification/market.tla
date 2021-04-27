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
         /\ bids = [p \in PAIR |-> c \in p |-> <<>>]
         /\ bonds = [p \in PAIR |-> c \in p |-> NoVal]
         

SubmitOrder == 
    /\ \E o \in Order :
        /\ orderQ’ = [orderQ EXCEPT ![{o.bid, o.ask}] = Append(@, o)
        /\ UNCHANGED liquidity
   
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
                    LET askAmount == (bondAsk * o.amount) \div bondBid
                    IN  \* Is there enough liquidity on ask bond?
                        /\ askAmount < bondAsk
                        \* Update bond with order
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
