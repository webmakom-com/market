------------------------------- MODULE Limit -------------------------------
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

Limit ==   
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
                /\  accounts' = [accounts EXCEPT 
                        ![headLimit.acct][ask] = 
                        @ - headLimit.amount
                    ]
                /\  limits' = [limits EXCEPT 
                        ![<<{ask, bid}, ask>>] = Tail(@)
                    ]
            ELSE
            \* AMM only has sufficient liquidity to fill part of the order
                /\  accounts' = [accounts EXCEPT
                        ![headLimit.acct][ask] =
                        @ - headLimit.amt
                    ]
                /\  limits' = [limits EXCEPT ![<<{ask, bid}, ask>>] = 
                        Append([
                            acct: headLimit.acct,
                            amt: headLimit.amt - bondBid,
                            exchrate: headLimit.exchrate
                        ], @)
                              
        ELSE UNCHANGED << >>

=============================================================================
\* Modification History
\* Last modified Tue Jul 20 22:46:01 CDT 2021 by Charles Dusek
\* Created Tue Jul 20 22:45:29 CDT 2021 by Charles Dusek
