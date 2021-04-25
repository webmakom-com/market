------------------------------- MODULE market -------------------------------
EXTENDS     Naturals, Sequences

CONSTANT    COIN,   \* Set of all coins
            PAIR   \* Set of all pairs of coins
           
VARIABLE    book,   \* Order Book
            bonds,  \* AMM Bond Curves

-----------------------------------------------------------------------------
NoVal ==    CHOOSE v : v \notin Nat

Init ==  /\ books = [c / COIN |-> [d \in COIN - c |-> {}]
         /\ bonds = [c / COIN |-> [d \in COIN - c |-> {}]

Book == [amount: Nat, bid: COIN, ask: COIN, exchrate: Nat]

Bond == [amount: Nat, bid: COIN, ask: COIN]

Order == Book \cup Bond

SubmitOrder == /\ \E o \in Order :
                  IF o.exchrate != {}
                  THEN /\ book’ = [book EXCEPT ![o.bid][o.ask] =
                                  Append(
                                    book[o.bid][o.ask],
                                    [
                                       amount: o.amount,
                                       exchrate: o.exchrate
                                    ]
                                   )]
                       /\ UNCHANGED bond
                  ELSE /\ bond’ = [bond EXCEPT ![o.bid][o.ask] =
                                  Append(
                                    bond[o.bid][o.ask],
                                    o.amount
                                   )]
                  



=============================================================================
\* Modification History
\* Last modified Tue Apr 20 22:17:38 CDT 2021 by djedi
\* Last modified Tue Apr 20 14:11:16 CDT 2021 by charlesd
\* Created Tue Apr 20 13:18:05 CDT 2021 by charlesd
