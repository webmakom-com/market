------------------------------ MODULE BidLimit ------------------------------
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
BidLimit ==
    /\  ctl = "Limit" 
    /\  LET bondAsk == bonds[pairPlusAsk]
            pair == pairPlusAsk[0]
            ask == pairPlusAsk[1]
            bid == { c \in pairPlusAsk[0] : c # pairPlusAsk[1] }
        IN  LET 
            bondExchrate ==         
                <<bond[<<pair, bid>>], bond[<<pair, ask>>]>>
            bondAsk == bonds[pairPlusAsk]
            bondBid == bonds[<<pair, bid>>]
            limitBid == limits[p][bid]
            stopAsk == stops[p][ask]
        IN  LET
            limitBidInverseExchrate == 
                <<limitsBid.exchrate[1], limitsBid.exchrate[0]>>
        IN
            CASE   GT(limitBidInverseExchrate, bondExchrate)    ->
                (***************************************************************)
                (* CASE 1.1: Inverse Exchange Rate of the head of the bid     *)
                (*           stops is less than the Exchange Rate of the head  *)
                (*           of the Ask Limits                              *)
                (***************************************************************)
                CASE    GT(limitBidInverseExchrate, stopAsk.exchrate) ->
                        LET bondBid == MaxBondBid(
                                stopAsk.exchrate, 
                                bondBid, 
                                bondAsk
                            )
                        IN  
                            LET strikeAskAmount == 
                                \* Is bondBid (bid amount) * exchrate
                                \* (ask/bid) enough to cover 
                                \* limitBid.amount (ask amount)
                                IF  limitBid.amount < bondBid * 
                                    (stopAsk.exchrate[1] / 
                                    stopAsk.exchrate[0]) 
                                THEN limitBid.amount
                                \* ELSE: limit ask is used as the exchrate that the AMM uses to trade
                                \* This allows the AMM to collect the difference between the exchange rate
                                \* defined by the balances of the AMM, and the exchange rate that enables
                                \* first ask limit order
                                \*
                                \* We do not consider enabling other stop loss orders as the first limit order
                                \* exchange rate dictates the upper bound before dependent books are reached
                                ELSE bondBid * (stopAsk.exchrate[1] / 
                                     stopAsk.exchrate[0])
                                \* strikeBidAmount (bid amount) ==
                                \* strikeAskAmount * exchrate 
                                \* (bid/ask)
                                strikeBidAmount == strikeAskAmount *
                                     (stopAsk.exchrate[0] / 
                                    stopAsk.exchrate[1]) 
                            IN  \* Remove head of bid stop book
                                /\ stops' = [stops EXCEPT ![<<p, ask>>] = Tail(@)]
                                /\ bonds' = [
                                                bonds EXCEPT 
                                                    ![<<p, ask>>] = @ + strikeBidAmount,
                                                    ![<<p, bid>>] = @ - strikeAskAmount
                                            ]
                                /\ accounts' = [accounts EXCEPT 
                                        ![limitBid.account][bid] = 
                                            [
                                                balance: @.balance + strikeBidAmount,
                                                positions: <<
                                                    @.positions[ask][0], 
                                                    Tail(@.positions[ask][1])
                                                >>
                                            ],
                                        
                                        
                                        
                                    \* Price charged for the ask coin is limitBid.exchrate
                                    \* AMM earns difference between limitBid.exchrate and bondExchrate
                                        ![limitBid.account][ask] =
                                            [
                                                balance: @.balance - strikeAskAmount,
                                                \* Balance positions such that limit and loss sequences sum
                                                \* the balance of coin in the account
                                                positions: Balance(bid, @.balance - strikeAskAmount, @.positions)
                                            ]
                                        
                                     ]
                (***********************************************************)
                (* CASE 1.2: Inverse Exchange Rate of the head of the bid *)
                (*           stops is greater than the Exchange Rate of the*)
                (*           head of the Ask Limits                     *)
                (***********************************************************)      
                []      LT(limitBidInverseExchrate, stopAsk.exchrate) ->
                        LET strikeExchrate == 
                            IF stopBidInverseExchrate < Head(Tail(limits[p][ask]))
                            THEN stopBidInverseExchrate
                            ELSE Head(Tail(limits[p][ask]))
                        IN
                        \* Execute stopAsk order
                        LET bondBid == MaxBondBid(
                                strikeExchrate, 
                                bondBid, 
                                bondAsk
                            )
                        IN  \* Is bondBid (bid amount) * exchrate
                            \* (ask/bid) enough to cover 
                            \* limitBid.amount (ask amount)
                            LET strikeAskAmount == 
                                \* Is bondBid enough to cover limitBid.amount?
                                IF  stopAsk.amount < bondBid * 
                                    (strikeExchrate[1] / 
                                    strikeExchrate[0]) 
                                THEN stopAsk.amount
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
                                /\  IF strikeAskAmount = stopAsk.amount
                                    THEN /\ limits' = [limits EXCEPT ![<<p, ask>>] = Tail(@)]
                                         /\ accounts' = [accounts EXCEPT 
                                            ![stopAsk.account][bid] = 
                                                [   
                                                    balance: @.balance + strikeBidAmount,
                                                    positions: <<
                                                        \* Remove head of 
                                                        Tail(@.positions[ask][0]), 
                                                        \* Stops
                                                        @.positions[ask][1]
                                                    >>
                                                ],
                                            ![stopAsk.account][ask] =
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
                                                ![stopAsk.account][bid] = 
                                                    [
                                                        balance: @.balance + strikeBidAmount,
                                                        positions: <<
                                                            \* Remove head of 
                                                            Append(
                                                                Tail(@.positions[ask][0]),
                                                                [
                                                                    account: stopAsk.account,
                                                                    amount: stopAsk.amount - strikeAskAmount,
                                                                    exchrate: stopAsk.exchrate
                                                                ]
                                                            ),
                                                            \* Stops
                                                            @.positions[ask][1]
                                                        >>
                                                    ],
                                                \* Price charged for the ask coin is limitBid.exchrate
                                                \* AMM earns difference between limitBid.exchrate and bondExchrate
                                                ![stopAsk.account][ask] =
                                                    [
                                                        balance: @.balance - strikeAskAmount,
                                                        \* Balance positions such that limit and loss sequences sum
                                                        \* the balance of coin in the account
                                                        positions: Balance(bid, @.balance - strikeAskAmount, @.positions)
                                                    ]
                                            ]
                                /\ UNCHANGED <<>>
                (***********************************************************)
                (* CASE 1.3: Inverse Exchange Rate of the head of the bid *)
                (*           stops is equal to the Exchange Rate of the    *)
                (*           head of the Ask Limits                     *)
                (***********************************************************)
                []      stopAsk.exchrate = limitBid.exchrate ->
                     \* In this case the exchrate does not change if equal amounts of ask
                     \* and bid coins are simulataneously exchanged.
                     \* AMM may exchange up the to least amount of the stopAsk or
                     \* the limitBid orders.
                    LET least == 
                        CHOOSE least \in { stopAsk, limitBid } : least.amount <
                        { stopAsk.amount, limitBid.amount } \ least.amount
                    IN
                        /\  IF stopAsk.amount = least.amount
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
                                        ![stopAsk.account][ask] = [
                                            balance: @.balance - strikeAskAmount,
                                            \* Balance positions such that limit and loss sequences sum
                                            \* the balance of coin in the account
                                            positions: Balance(ask, @.balance - strikeAskAmount, @.positions)
                                        ],
                                        ![stopAsk.account][bid] = [
                                            balance: @.balance + strikeBidAmount
                                        ],
                                        ![bidLimit.account][bid] = [
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
                                        ![stopAsk.account] = Tail(@)
                                            
                                        ![bidLimit.account] = 
            [] OTHER -> ctl' = "Stable"


=============================================================================
\* Modification History
\* Last modified Sun Jul 18 21:33:00 CDT 2021 by Charles Dusek
\* Created Sun Jul 18 21:24:55 CDT 2021 by Charles Dusek
