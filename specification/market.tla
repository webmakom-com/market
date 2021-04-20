------------------------------- MODULE market -------------------------------
CONSTANT    COIN,   \* Set of all coins
            PAIR,   \* Set of all pairs of coins
            USER,   \* Set of all users
            PRICE   \* Set of all possible prices

VARIABLE    book,   \* Order Book
            bonds,  \* AMM Bond Curves
            wallet  \* User wallets

-----------------------------------------------------------------------------
NoVal ==    CHOOSE v : v \notin Val

Order == {   

=============================================================================
\* Modification History
\* Last modified Tue Apr 20 14:11:16 CDT 2021 by charlesd
\* Created Tue Apr 20 13:18:05 CDT 2021 by charlesd
