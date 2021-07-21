------------------------------ MODULE AskStop ------------------------------
EXTENDS     Naturals, Sequences, SequencesExt

CONSTANT    Account,    \* Set of all accounts
            Coin,       \* Set of all coins
            Denominator \* Set of all possible denominators. Precision of 
                        \* fractions is defined by denominator constant.
           
VARIABLE    accounts,
            ask,
            bid,
            limits,     \* Limit Order Books
            stops,      \* Stop Loss Order Books
            bonds,          \* AMM Bond Curves
            orderQ,         \* Sequenced queue of orders
            pairPlusAsk  \* Current Pair plus Ask Coin 

-----------------------------------------------------------------------------

IF  LT(
        Head(stops[<<{ask, bid}, ask>>]).exchrate,
        <<pools[<<{ask, bid}, bid>>],pools[<<{ask, bid}, ask>>]>>
    )
THEN
    /\
ELSE
                LET bondBid == MaxBondBid(limitAsk.exchrate, bondWeak, bondAsk)
[] OTHER -> ctl' = "AskStop"   
=============================================================================
\* Modification History
\* Last modified Mon Jul 19 22:32:31 CDT 2021 by Charles Dusek
\* Created Sun Jul 18 21:26:21 CDT 2021 by Charles Dusek
