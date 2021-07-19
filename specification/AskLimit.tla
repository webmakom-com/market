------------------------------ MODULE AskLimit ------------------------------
EXTENDS     Naturals, Sequences, SequencesExt, MarketHelpers

CONSTANT    Account,    \* Set of all accounts
            Coin,       \* Set of all coins
            Denominator \* Set of all possible denominators. Precision of 
                        \* fractions is defined by denominator constant.
           
VARIABLE    limitBooks,     \* Limit Order Books
            stopBooks,      \* Stop Loss Order Books
            bonds,          \* AMM Bond Curves
            orderQ,         \* Sequenced queue of orders
            pairPlusAsk  \* Current Pair plus Ask Coin 

-----------------------------------------------------------------------------

AskLimit ==   IF  LT(
    Head(limits[<<{ask, bid}, ask>>]).exchrate,
    <<pools[<<{ask, bid}, bid>>],pools[<<{ask, bid}, ask>>]>>
)
THEN
    IF  MaxBondBid() >= Head(limits[<<{ask, bid}, ask>>]).amount
    THEN
        /\  limits' = [limits EXCEPT ![<<{ask, bid}, ask>>] = Tail(@)]
        /\  accounts' = [accounts EXCEPT 
            ![Head(limits[<<{ask, bid}, ask>>]).acct][ask] = 
            @ - Head(limits[<<{ask, bid}, ask>>]).amount
            
ELSE

[] OTHER -> ctl' = "AskStop"          

=============================================================================
\* Modification History
\* Last modified Mon Jul 19 18:06:09 CDT 2021 by Charles Dusek
\* Created Sun Jul 18 21:25:28 CDT 2021 by Charles Dusek
