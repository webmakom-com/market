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

Init ==  /\ orderQ = [PAIR |-> <<>>]
         /\ bids = [PAIR |-> COIN |-> <<>>]
         /\ liquidity = [PAIR |-> {}]
         

SubmitOrder == /\ \E o \in Order :
                  /\ orderQ’ = [orderQ EXCEPT ![{o.bid, o.ask}] =
                                Append(@, o)]
                  /\ UNCHANGED liquidity
   
ProcessOrder(pair) =    /\ orderQ[pair] != <<>>
                        /\ Let o = Head(orderQ[pair])
                        \/ /\ o.exchrate != {}
                           \/ /\ Head(bids[pair][o.bid]).exchrate 
                                 > o.exchrate
                           \/ /\ Head(bids[pair][o.bid]).exchrate 
                                 = o.exchrate
                           \/ /\ bids[pair][o.ask] != <<>>
                              /\
                           \/ /\ bids[pair][o.ask] = <<>>
                  



=============================================================================
\* Modification History
\* Last modified Tue Apr 20 22:17:38 CDT 2021 by djedi
\* Last modified Tue Apr 20 14:11:16 CDT 2021 by charlesd
\* Created Tue Apr 20 13:18:05 CDT 2021 by charlesd
