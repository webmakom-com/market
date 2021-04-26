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

Init ==  /\ orderQ = [PAIR |-> <<>>]
         /\ bids = [PAIR |-> COIN |-> <<>>]
         /\ liquidity = [PAIR |-> Pool]
         

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
        
                \* Is book order exchrate greater than
                \* the head of the bid book?
                \/  /\ Head(bids[pair][o.bid]).exchrate 
                        > o.exchrate
                
                \* Is book order exchrate equal to head
                \* of the bid book?
                \/  /\ Head(bids[pair][o.bid]).exchrate 
                        = o.exchrate
                
                
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

            \* Is there liquidity?
            /\ LET l == CHOOSE l \in liquidity[pair] :

            \* Let askAmount be the amount of ask coin
            \* corresponding to the amount of bid coin
            /\ LET askAmount = 
                  



=============================================================================
\* Modification History
\* Last modified Tue Apr 20 22:17:38 CDT 2021 by djedi
\* Last modified Tue Apr 20 14:11:16 CDT 2021 by charlesd
\* Created Tue Apr 20 13:18:05 CDT 2021 by charlesd
