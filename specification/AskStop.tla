------------------------------ MODULE AskStop ------------------------------
EXTENDS     Naturals, Sequences, SequencesExt

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

CASE        limitAsk.exchrate.LT(bondExchrate)       ->
                LET bondBid == MaxBondBid(limitAsk.exchrate, bondWeak, bondAsk)
[] OTHER -> ctl' = "AskStop"   
=============================================================================
\* Modification History
\* Last modified Sun Jul 18 21:55:35 CDT 2021 by Charles Dusek
\* Created Sun Jul 18 21:26:21 CDT 2021 by Charles Dusek
