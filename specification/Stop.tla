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
            headStop == Head(stops[pairPlusBid]) IN
        IF  LT(
            headStop.exchrate,
            <<pools[pairPlusAsk],pools[pairPlusBid]>>
        )
        THEN
            LET poolBid == MaxPoolBid(
                    Head(stops[pairPlusBid]).exchrate,
                    ask,
                    bid
                ) IN
            IF poolBid >= headStop.amt
            \* AMM has sufficient liquidity to complete order
            THEN
                /\  accounts' = [accounts EXCEPT 
                        ![headStop.acct][ask] = 
                        @ - headStop.amount
                    ]
                /\  stops' = [stops EXCEPT 
                        ![pairPlusBid] = Tail(@)
                    ]
            ELSE
            \* AMM only has sufficient liquidity to fill part of the order
                /\  accounts' = [accounts EXCEPT
                        ![headStop.acct][ask] =
                        @ - headStop.amt
                    ]
                /\  stops' = [
                        stops EXCEPT ![pairPlusBid] = 
                            Append([
                                acct: headStop.acct,
                                amt: headStop.amt - poolBid,
                                exchrate: headStop.exchrate
                        ], @)
                    ]
                              
        ELSE UNCHANGED << accounts, ask, bid, stops, pools >>

=============================================================================
\* Modification History
\* Last modified Thu Jul 22 20:26:49 CDT 2021 by Charles Dusek
\* Created Wed Jul 21 12:39:56 CDT 2021 by Charles Dusek
