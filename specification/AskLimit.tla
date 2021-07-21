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

AskLimit ==   
    /\  LET headLimit == Head(limits[<<{ask, bid}, ask>>]) IN
        IF  LT(
            headLimit.exchrate,
            <<pools[<<{ask, bid}, bid>>],pools[<<{ask, bid}, ask>>]>>
        )
        THEN
            LET bondBid == MaxBondBid(
                    Head(limits[<<{ask, bid}, ask>>]).exchrate,
                    bid,
                    ask
                ) IN
            IF bondBid >= headLimit.amount
            \* AMM has sufficient liquidity to complete order
            THEN
                /\  limits' = [limits EXCEPT ![<<{ask, bid}, ask>>] = Tail(@)]
                /\  accounts' = [accounts EXCEPT 
                    ![headLimit.acct][ask] = 
                        @ - headLimit.amount
                    ]
            ELSE
            \* AMM only has sufficient liquidity to fill part of the order
                /\  limits' = [limits EXCEPT ![<<{ask, bid}, ask>>] = 
                        Append([
                            acct: Head(limits[<<{ask, bid}, ask>>]).acct,
                            amt: Head(limits[<<{ask, bid}, ask>>]).amt - ,
                            exchrate: ExchRateType
                        ]
                              
        ELSE

[] OTHER -> ctl' = "AskStop"          

=============================================================================
\* Modification History
\* Last modified Tue Jul 20 22:35:40 CDT 2021 by Charles Dusek
\* Created Sun Jul 18 21:25:28 CDT 2021 by Charles Dusek
