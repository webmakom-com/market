------------------------------- MODULE Limit -------------------------------
EXTENDS     Naturals, Sequences, SequencesExt, MarketHelpers

CONSTANT    Coin,       \* Set of all coins
            Denominator \* Set of all possible denominators. Precision of 
                        \* fractions is defined by denominator constant.
           
VARIABLE    accounts,   \* Exchange Accounts
            ask,        \* Ask Coin
            bid,        \* Bid Coin
            limits,     \* Limit Order Books
            pools       \* AMM Pools 

-----------------------------------------------------------------------------

Limit ==   
    /\  LET pairPlusAsk == <<{ask, bid}, ask>>
            pairPlusBid == <<{ask, bid}, bid>>
            headLimit == Head(limits[pairPlusBid]) IN
        IF  LT(
            headLimit.exchrate,
            <<pools[pairPlusAsk],pools[pairPlusBid]>>
        )
        THEN
            LET poolBid == MaxPoolBid(
                    Head(limits[pairPlusBid]).exchrate,
                    ask,
                    bid
                ) IN
            IF poolBid >= headLimit.amt
            \* AMM has sufficient liquidity to complete order
            THEN
                /\  accounts' = [accounts EXCEPT 
                        ![headLimit.acct][ask] = 
                        @ - headLimit.amount
                    ]
                /\  limits' = [limits EXCEPT 
                        ![pairPlusBid] = Tail(@)
                    ]
            ELSE
            \* AMM only has sufficient liquidity to fill part of the order
                /\  accounts' = [accounts EXCEPT
                        ![headLimit.acct][ask] =
                        @ - headLimit.amt
                    ]
                /\  limits' = [
                        limits EXCEPT ![pairPlusBid] = 
                            Append([
                                acct: headLimit.acct,
                                amt: headLimit.amt - poolBid,
                                exchrate: headLimit.exchrate
                        ], @)
                    ]
                              
        ELSE UNCHANGED << accounts, ask, bid, limits, pools >>

=============================================================================
\* Modification History
\* Last modified Wed Jul 21 12:46:20 CDT 2021 by Charles Dusek
\* Created Tue Jul 20 22:45:29 CDT 2021 by Charles Dusek
