-------------------------------- MODULE Stop --------------------------------
EXTENDS     Naturals, Sequences, SequencesExt, MarketHelpers

CONSTANT    Coin,       \* Set of all coins
            Denominator \* Set of all possible denominators. Precision of 
                        \* fractions is defined by denominator constant.
           
VARIABLE    accounts,   \* Exchange Accounts
            ask,        \* Ask Coin
            bid,        \* Bid Coin
            stops,      \* Stop Loss Order Books
            pools       \* AMM Pools 
            
-----------------------------------------------------------------------------

Stop ==   
    /\  LET pairPlusAsk == <<{ask, bid}, ask>>
            pairPlusBid == <<{ask, bid}, bid>>
            headLimit == Head(stops[pairPlusBid]) IN
        IF  LT(
            headLimit.exchrate,
            <<pools[pairPlusAsk],pools[pairPlusBid]>>
        )
        THEN
            LET poolBid == MaxPoolBid(
                    Head(stops[pairPlusBid]).exchrate,
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
                /\  stops' = [stops EXCEPT 
                        ![pairPlusBid] = Tail(@)
                    ]
            ELSE
            \* AMM only has sufficient liquidity to fill part of the order
                /\  accounts' = [accounts EXCEPT
                        ![headLimit.acct][ask] =
                        @ - headLimit.amt
                    ]
                /\  stops' = [
                        stops EXCEPT ![pairPlusBid] = 
                            Append([
                                acct: headLimit.acct,
                                amt: headLimit.amt - poolBid,
                                exchrate: headLimit.exchrate
                        ], @)
                    ]
                              
        ELSE UNCHANGED << accounts, ask, bid, stops, pools >>

=============================================================================
\* Modification History
\* Last modified Wed Jul 21 12:46:30 CDT 2021 by Charles Dusek
\* Created Wed Jul 21 12:39:56 CDT 2021 by Charles Dusek
