------------------------------- MODULE market -------------------------------
EXTENDS     Naturals, Sequences

CONSTANT    COIN,   \* Set of all coins
            PAIR   \* Set of all pairs of coins
           
VARIABLE    book,   \* Order Book
            bonds,  \* AMM Bond Curves
            wallet  \* User wallets

-----------------------------------------------------------------------------
NoVal ==    CHOOSE v : v \notin Nat

Order == [amount: Nat, coin: COIN, pair: PAIR, price: Nat]

Bond == [amount: Nat, coin: COIN, pair: PAIR]

=============================================================================
\* Modification History
\* Last modified Tue Apr 20 22:17:38 CDT 2021 by djedi
\* Last modified Tue Apr 20 14:11:16 CDT 2021 by charlesd
\* Created Tue Apr 20 13:18:05 CDT 2021 by charlesd
