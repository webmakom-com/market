------------------------------ MODULE BidStop ------------------------------
EXTENDS     Naturals, Sequences, SequencesExt

CONSTANT    Account,    \* Set of all accounts
            Coin,       \* Set of all coins
            Denominator \* Set of all possible denominators. Precision of 
                        \* fractions is defined by denominator constant.
           
VARIABLE    accounts,
            ask,
            bid,
            limitBooks,     \* Limit Order Books
            stopBooks,      \* Stop Loss Order Books
            bonds,          \* AMM Bond Curves
            orderQ,         \* Sequenced queue of orders
            pairPlusAsk  \* Current Pair plus Ask Coin 

-----------------------------------------------------------------------------

\* Explore mutual recursion, but for now, will use ask and bid to differentiate
BidStop ==
    /\  ctl = "BidStop" 
    /\  LET bondAsk == bonds[pairPlusAsk]
            pair == pairPlusAsk[0]
            ask == pairPlusAsk[1]
            bid == { c \in pairPlusAsk[0] : c # pairPlusAsk[1] }
        IN  LET 
            bondAsk == bonds[pairPlusAsk]
            bondBid == bonds[<<pair, bid>>]
            limitAsk = limits[p][ask]
            stopBid = stops[p][pairPlusAsk[1]]
            bondExchrate ==         
                <<bond[<<pair, bid>>], bond[<<pair, ask>>]>>
            stopBidInverseExchrate == 
                <<stopsBid.exchrate[1], stopsBid.exchrate[0]>>
        IN
            CASE   LT(stopBidInverseExchrate, bondExchrate)    ->
                (***************************************************************)
                (* CASE 1.1: Inverse Exchange Rate of the head of the Bid     *)
                (*           stops is less than the Exchange Rate of the head  *)
                (*           of the Ask Limits                              *)
                (***************************************************************)
                CASE    LT(stopBidInverseExchrate, limitAsk.exchrate) ->
                        LET bondBid == MaxBondBid(
                                limitAsk.exchrate, 
                                bondBid, 
                                bondAsk
                            )
                        IN  
                            LET strikeAskAmount == 
                                \* Is bondBid (bid amount) * exchrate
                                \* (ask/bid) enough to cover 
                                \* stopBid.amount (ask amount)
                                IF  stopBid.amount < bondBid * 
                                    (limitAsk.exchrate[1] / 
                                    limitAsk.exchrate[0]) 
                                THEN stopBid.amount
                                \* ELSE: limit ask is used as the exchrate that the AMM uses to trade
                                \* This allows the AMM to collect the difference between the exchange rate
                                \* defined by the balances of the AMM, and the exchange rate that enables
                                \* first ask limit order
                                \*
                                \* We do not consider enabling other stop loss orders as the first limit order
                                \* exchange rate dictates the upper bound before dependent books are reached
                                ELSE bondBid * (limitAsk.exchrate[1] / 
                                     limitAsk.exchrate[0])
                                \* strikeBidAmount (bid amount) ==
                                \* strikeAskAmount * exchrate 
                                \* (bid/ask)
                                strikeBidAmount == strikeAskAmount *
                                     (limitAsk.exchrate[0] / 
                                    limitAsk.exchrate[1]) 
                            IN  \* Remove head of bid stop book
                                /\ stops' = [stops EXCEPT ![<<p, ask>>] = Tail(@)]
                                /\ bonds' = [
                                                bonds EXCEPT 
                                                    ![<<p, ask>>] = @ + strikeBidAmount,
                                                    ![<<p, bid>>] = @ - strikeAskAmount
                                            ]
                                /\ accounts' = [accounts EXCEPT 
                                        ![stopBid.account][bid] = 
                                            [
                                                balance: @.balance + strikeBidAmount,
                                                positions: <<
                                                    @.positions[ask][0], 
                                                    Tail(@.positions[ask][1])
                                                >>
                                            ],
                                        
                                        
                                        
                                    \* Price charged for the ask coin is stopBid.exchrate
                                    \* AMM earns difference between stopBid.exchrate and bondExchrate
                                        ![stopBid.account][ask] =
                                            [
                                                balance: @.balance - strikeAskAmount,
                                                \* Balance positions such that limit and loss sequences sum
                                                \* the balance of coin in the account
                                                positions: Balance(bid, @.balance - strikeAskAmount, @.positions)
                                            ]
                                        
                                     ]
                (***********************************************************)
                (* CASE 1.2: Inverse Exchange Rate of the head of the Bid *)
                (*           stops is greater than the Exchange Rate of the*)
                (*           head of the Ask Limits                     *)
                (***********************************************************)      
                []      GT(stopBidInverseExchrate, limitAsk.exchrate) ->
                        LET strikeExchrate == 
                            IF stopBidInverseExchrate < Head(Tail(limits[p][ask]))
                            THEN stopBidInverseExchrate
                            ELSE Head(Tail(limits[p][ask]))
                        IN
                        \* Execute limitAsk order
                        LET bondBid == MaxBondBid(
                                strikeExchrate, 
                                bondBid, 
                                bondAsk
                            )
                        IN  \* Is bondBid (bid amount) * exchrate
                            \* (ask/bid) enough to cover 
                            \* stopBid.amount (ask amount)
                            LET strikeAskAmount == 
                                \* Is bondBid enough to cover stopBid.amount?
                                IF  limitAsk.amount < bondBid * 
                                    (strikeExchrate[1] / 
                                    strikeExchrate[0]) 
                                THEN limitAsk.amount
                                ELSE bondBid * 
                                    (strikeExchrate[1] / 
                                    strikeExchrate[0])
                                \* strikeBidAmount (bid amount) ==
                                \* strikeAskAmount * exchrate 
                                \* (bid/ask)
                                strikeBidAmount ==
                                    strikeAskAmount * 
                                    (strikeExchrate[0] / 
                                    strikeExchrate[1])
                            IN  \*  Remove limit position or update balance
                                /\ bonds' = [
                                                bonds EXCEPT 
                                                    ![<<p, ask>>] = @ + strikeAskAmount,
                                                    ![<<p, bid>>] = @ - strikeBidAmount
                                            ]
                                /\  IF strikeAskAmount = limitAsk.amount
                                    THEN /\ limits' = [limits EXCEPT ![<<p, ask>>] = Tail(@)]
                                         /\ accounts' = [accounts EXCEPT 
                                            ![limitAsk.account][bid] = 
                                                [   
                                                    balance: @.balance + strikeBidAmount,
                                                    positions: <<
                                                        \* Remove head of 
                                                        Tail(@.positions[ask][0]), 
                                                        \* Stops
                                                        @.positions[ask][1]
                                                    >>
                                                ],
                                            ![limitAsk.account][ask] =
                                                [
                                                    balance: @.balance - strikeAskAmount,
                                                    \* Balance function needed to adjust 
                                                    \* positions such that limit and loss 
                                                    \* sequences sum the balance of coin 
                                                    \* in the account
                                                    positions: Balance(bid, @.balance - strikeAskAmount, @.positions)
                                                ]
                                                ]
                                         
                                    ELSE /\ limits' = [limits EXCEPT ![<<p, ask>>] = UNION {
                                            [
                                                account: @.account,
                                                amount: @.amount - strikeAskAmount,
                                                positions: @.positions \* Need to update positions 
                                            ],
                                            Tail(@)}
                                            ]
                                         /\ accounts' = [accounts EXCEPT 
                                                ![limitAsk.account][bid] = 
                                                    [
                                                        balance: @.balance + strikeBidAmount,
                                                        positions: <<
                                                            \* Remove head of 
                                                            Append(
                                                                Tail(@.positions[ask][0]),
                                                                [
                                                                    account: limitAsk.account,
                                                                    amount: limitAsk.amount - strikeAskAmount,
                                                                    exchrate: limitAsk.exchrate
                                                                ]
                                                            ),
                                                            \* Stops
                                                            @.positions[ask][1]
                                                        >>
                                                    ],
                                                \* Price charged for the ask coin is stopBid.exchrate
                                                \* AMM earns difference between stopBid.exchrate and bondExchrate
                                                ![limitAsk.account][ask] =
                                                    [
                                                        balance: @.balance - strikeAskAmount,
                                                        \* Balance positions such that limit and loss sequences sum
                                                        \* the balance of coin in the account
                                                        positions: Balance(bid, @.balance - strikeAskAmount, @.positions)
                                                    ]
                                            ]
                                /\ UNCHANGED <<>>
                (***********************************************************)
                (* CASE 1.3: Inverse Exchange Rate of the head of the Bid *)
                (*           stops is equal to the Exchange Rate of the    *)
                (*           head of the Ask Limits                     *)
                (***********************************************************)
                []      limitAsk.exchrate = stopBid.exchrate ->
                     \* In this case the exchrate does not change if equal amounts of ask
                     \* and bid coins are simulataneously exchanged.
                     \* AMM may exchange up the to least amount of the limitAsk or
                     \* the stopBid orders.
                    LET least == 
                        CHOOSE least \in { limitAsk, stopBid } : least.amount <
                        { limitAsk.amount, stopBid.amount } \ least.amount
                    IN
                        /\  IF limitAsk.amount = least.amount
                            THEN    /\ limits' = [limits EXCEPT ![p][ask] = Tail(@)]
                                    /\ stops' = [stops EXCEPT ![p][bid] = Append (
                                            [
                                                account: Head(@).account,
                                                amount: Head(@).amount - least.amount,
                                                exchrate: Head(@).exchrate
                                            ], 
                                            Tail(@)
                                        )]
                                    /\ accounts' = [accounts EXCEPT 
                                        ![limitAsk.account][ask] = [
                                            balance: @.balance - strikeAskAmount,
                                            \* Balance positions such that limit and loss sequences sum
                                            \* the balance of coin in the account
                                            positions: Balance(ask, @.balance - strikeAskAmount, @.positions)
                                        ],
                                        ![limitAsk.account][bid] = [
                                            balance: @.balance + strikeBidAmount
                                        ],
                                        ![bidStop.account][bid] = [
                                            balance: @.balance - strikeAskAmount,
                                            \* Balance positions such that limit and loss sequences sum
                                            \* the balance of coin in the account
                                            positions: Balance(bid, @.balance - strikeAskAmount, @.positions)
                                        ]
                                       ]
                            ELSE    /\ limits' = [limits EXCEPT ![p][ask] = Append (
                                        [
                                            account: Head(@).account,
                                            amount: Head(@).amount - least.amount,
                                            exchrate: Head(@).exchrate
                                        ], 
                                        Tail(@)
                                       )]
                                    /\ stops' = [stops EXCEPT ![p][bid] = Tail(@)
                                    /\ accounts' = [accounts EXCEPT 
                                        ![limitAsk.account] =
                                        ![bidStop.account] = 
            [] OTHER -> ctl'= "AskLimit"

=============================================================================
\* Modification History
\* Last modified Sun Jul 18 21:36:16 CDT 2021 by Charles Dusek
\* Created Sun Jul 18 21:26:38 CDT 2021 by Charles Dusek
