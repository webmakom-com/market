---------------------------- MODULE StrongLimit ----------------------------
EXTENDS     Naturals, Sequences, SequencesExt

CONSTANT    Account,    \* Set of all accounts
            Coin,       \* Set of all coins
            Denominator \* Set of all possible denominators. Precision of 
                        \* fractions is defined by denominator constant.
           
VARIABLE    limitBooks,     \* Limit Order Books
            stopBooks,      \* Stop Loss Order Books
            bonds,          \* AMM Bond Curves
            orderQ,         \* Sequenced queue of orders
            pairPlusStrong  \* Current Pair plus Strong Coin 

-----------------------------------------------------------------------------

CASE        limitStrong.exchrate.LT(bondExchrate)       ->
                LET bondBid == MaxBondBid(limitStrong.exchrate, bondWeak, bondStrong)
[] OTHER -> ctl' = "StrongStop"            
=============================================================================
\* Modification History
\* Last modified Fri Jul 16 22:17:20 CDT 2021 by Charles Dusek
\* Created Fri Jul 16 22:11:44 CDT 2021 by Charles Dusek
