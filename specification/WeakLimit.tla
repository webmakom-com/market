----------------------------- MODULE WeakLimit -----------------------------
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
\* Explore mutual recursion, but for now, will use strong and weak to differentiate
WeakStop ==
    /\  ctl = "WeakStop" 
    /\  LET bondStrong == bonds[pairPlusStrong]
            pair == pairPlusStrong[0]
            strong == pairPlusStrong[1]
            weak == { c \in pairPlusStrong[0] : c # pairPlusStrong[1] } IN
        IN  LET 
            bondStrong == bonds[pairPlusStrong]
            bondWeak == bonds[<<pair, weak>>]
            limitStrong = limits[p][strong]
            stopWeak = stops[p][pairPlusStrong[1]]
            bondExchrate ==         
                <<bond[<<pair, weak>>], bond[<<pair, strong>>]>>
            stopWeakInverseExchrate == 
                <<stopsWeak.exchrate[1], stopsWeak.exchrate[0]>>
        IN
            CASE   LT(stopWeakInverseExchrate, bondExchrate)    ->
                (***************************************************************)
                (* CASE 1.1: Inverse Exchange Rate of the head of the Weak     *)
                (*           stops is less than the Exchange Rate of the head  *)
                (*           of the Strong Limits                              *)
                (***************************************************************)

CASE    weakLimitHead.exchrate.GT(strongStopHead.exchrate) ->
                []      weakLimitHead.exchrate.LT(strongStopHead.exchrate) ->
                []      weakLimitHead.exchrate = strongStopHead.exchrate ->

CASE 
    /\ ctl' = "WeakStop"
[] OTHER -> ctl' = "Stable"
=============================================================================
\* Modification History
\* Last modified Fri Jul 16 22:21:38 CDT 2021 by Charles Dusek
\* Created Fri Jul 16 22:17:43 CDT 2021 by Charles Dusek
