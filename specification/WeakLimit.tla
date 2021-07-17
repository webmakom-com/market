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
WeakLimit ==
    /\  ctl = "WeakStop" 
    /\  LET bondStrong == bonds[pairPlusStrong]
            pair == pairPlusStrong[0]
            strong == pairPlusStrong[1]
            weak == { c \in pairPlusStrong[0] : c # pairPlusStrong[1] } IN
        IN  LET 
            bondExchrate ==         
                <<bond[<<pair, weak>>], bond[<<pair, strong>>]>>
            bondStrong == bonds[pairPlusStrong]
            bondWeak == bonds[<<pair, weak>>]
            limitWeak = limits[p][weak]
            stopStrong = stops[p][strong]
        IN  LET
            limitWeakInverseExchrate == 
                <<limitsWeak.exchrate[1], limitsWeak.exchrate[0]>>
        IN
            CASE   GT(limitWeakInverseExchrate, bondExchrate)    ->
                (***************************************************************)
                (* CASE 1.1: Inverse Exchange Rate of the head of the Weak     *)
                (*           stops is less than the Exchange Rate of the head  *)
                (*           of the Strong Limits                              *)
                (***************************************************************)
                CASE    LT(limitWeakInverseExchrate, limitStrong.exchrate) ->
                        LET bondBid == MaxBondBid(
                                limitStrong.exchrate, 
                                bondWeak, 
                                bondStrong
                            )
                        IN  
                            LET strikeStrongAmount == 
                                \* Is bondBid (weak amount) * exchrate
                                \* (strong/weak) enough to cover 
                                \* stopWeak.amount (strong amount)
                                IF  stopWeak.amount < bondBid * 
                                    (limitStrong.exchrate[1] / 
                                    limitStrong.exchrate[0]) 
                                THEN stopWeak.amount
                                \* ELSE: limit strong is used as the exchrate that the AMM uses to trade
                                \* This allows the AMM to collect the difference between the exchange rate
                                \* defined by the balances of the AMM, and the exchange rate that enables
                                \* first strong limit order
                                \*
                                \* We do not consider enabling other stop loss orders as the first limit order
                                \* exchange rate dictates the upper bound before dependent books are reached
                                ELSE bondBid * (limitStrong.exchrate[1] / 
                                     limitStrong.exchrate[0])
                                \* strikeWeakAmount (weak amount) ==
                                \* strikeStrongAmount * exchrate 
                                \* (weak/strong)
                                strikeWeakAmount == strikeStrongAmount *
                                     (limitStrong.exchrate[0] / 
                                    limitStrong.exchrate[1]) 
                            IN  \* Remove head of weak stop book
                                /\ stops' = [stops EXCEPT ![<<p, strong>>] = Tail(@)]
                                /\ bonds' = [
                                                bonds EXCEPT 
                                                    ![<<p, strong>>] = @ + strikeWeakAmount,
                                                    ![<<p, weak>>] = @ - strikeStrongAmount
                                            ]
                                /\ accounts' = [accounts EXCEPT 
                                        ![stopWeak.account][weak] = 
                                            [
                                                balance: @.balance + strikeWeakAmount,
                                                positions: <<
                                                    @.positions[strong][0], 
                                                    Tail(@.positions[strong][1])
                                                >>
                                            ],
                                        
                                        
                                        
                                    \* Price charged for the ask coin is stopWeak.exchrate
                                    \* AMM earns difference between stopWeak.exchrate and bondExchrate
                                        ![stopWeak.account][strong] =
                                            [
                                                balance: @.balance - strikeStrongAmount,
                                                \* Balance positions such that limit and loss sequences sum
                                                \* the balance of coin in the account
                                                positions: Balance(weak, @.balance - strikeStrongAmount, @.positions)
                                            ]
                                        
                                     ]
                (***********************************************************)
                (* CASE 1.2: Inverse Exchange Rate of the head of the Weak *)
                (*           stops is greater than the Exchange Rate of the*)
                (*           head of the Strong Limits                     *)
                (***********************************************************)      
                []      GT(stopWeakInverseExchrate, limitStrong.exchrate) ->
                        LET strikeExchrate == 
                            IF stopWeakInverseExchrate < Head(Tail(limits[p][strong]))
                            THEN stopWeakInverseExchrate
                            ELSE Head(Tail(limits[p][strong]))
                        IN
                        \* Execute limitStrong order
                        LET bondBid == MaxBondBid(
                                strikeExchrate, 
                                bondWeak, 
                                bondStrong
                            )
                        IN  \* Is bondBid (weak amount) * exchrate
                            \* (strong/weak) enough to cover 
                            \* stopWeak.amount (strong amount)
                            LET strikeStrongAmount == 
                                \* Is bondBid enough to cover stopWeak.amount?
                                IF  limitStrong.amount < bondBid * 
                                    (strikeExchrate[1] / 
                                    strikeExchrate[0]) 
                                THEN limitStrong.amount
                                ELSE bondBid * 
                                    (strikeExchrate[1] / 
                                    strikeExchrate[0])
                                \* strikeWeakAmount (weak amount) ==
                                \* strikeStrongAmount * exchrate 
                                \* (weak/strong)
                                strikeWeakAmount ==
                                    strikeStrongAmount * 
                                    (strikeExchrate[0] / 
                                    strikeExchrate[1])
                            IN  \*  Remove limit position or update balance
                                /\ bonds' = [
                                                bonds EXCEPT 
                                                    ![<<p, strong>>] = @ + strikeStrongAmount,
                                                    ![<<p, weak>>] = @ - strikeWeakAmount
                                            ]
                                /\  IF strikeStrongAmount = limitStrong.amount
                                    THEN /\ limits' = [limits EXCEPT ![<<p, strong>>] = Tail(@)]
                                         /\ accounts' = [accounts EXCEPT 
                                            ![limitStrong.account][weak] = 
                                                [   
                                                    balance: @.balance + strikeWeakAmount,
                                                    positions: <<
                                                        \* Remove head of 
                                                        Tail(@.positions[strong][0]), 
                                                        \* Stops
                                                        @.positions[strong][1]
                                                    >>
                                                ],
                                            ![limitStrong.account][strong] =
                                                [
                                                    balance: @.balance - strikeStrongAmount,
                                                    \* Balance function needed to adjust 
                                                    \* positions such that limit and loss 
                                                    \* sequences sum the balance of coin 
                                                    \* in the account
                                                    positions: Balance(weak, @.balance - strikeStrongAmount, @.positions)
                                                ]
                                                ]
                                         
                                    ELSE /\ limits' = [limits EXCEPT ![<<p, strong>>] = UNION {
                                            [
                                                account: @.account,
                                                amount: @.amount - strikeStrongAmount,
                                                positions: @.positions \* Need to update positions 
                                            ],
                                            Tail(@)}
                                            ]
                                         /\ accounts' = [accounts EXCEPT 
                                                ![limitStrong.account][weak] = 
                                                    [
                                                        balance: @.balance + strikeWeakAmount,
                                                        positions: <<
                                                            \* Remove head of 
                                                            Append(
                                                                Tail(@.positions[strong][0]),
                                                                [
                                                                    account: limitStrong.account,
                                                                    amount: limitStrong.amount - strikeStrongAmount,
                                                                    exchrate: limitStrong.exchrate
                                                                ]
                                                            ),
                                                            \* Stops
                                                            @.positions[strong][1]
                                                        >>
                                                    ],
                                                \* Price charged for the ask coin is stopWeak.exchrate
                                                \* AMM earns difference between stopWeak.exchrate and bondExchrate
                                                ![limitStrong.account][strong] =
                                                    [
                                                        balance: @.balance - strikeStrongAmount,
                                                        \* Balance positions such that limit and loss sequences sum
                                                        \* the balance of coin in the account
                                                        positions: Balance(weak, @.balance - strikeStrongAmount, @.positions)
                                                    ]
                                            ]
                                /\ UNCHANGED <<>>
                (***********************************************************)
                (* CASE 1.3: Inverse Exchange Rate of the head of the Weak *)
                (*           stops is equal to the Exchange Rate of the    *)
                (*           head of the Strong Limits                     *)
                (***********************************************************)
                []      limitStrong.exchrate = stopWeak.exchrate ->
                     \* In this case the exchrate does not change if equal amounts of ask
                     \* and bid coins are simulataneously exchanged.
                     \* AMM may exchange up the to least amount of the limitStrong or
                     \* the stopWeak orders.
                    LET least == 
                        CHOOSE least \in { limitStrong, stopWeak } : least.amount <
                        { limitStrong.amount, stopWeak.amount } \ least.amount
                    IN
                        /\  IF limitStrong.amount = least.amount
                            THEN    /\ limits' = [limits EXCEPT ![p][strong] = Tail(@)]
                                    /\ stops' = [stops EXCEPT ![p][weak] = Append (
                                            [
                                                account: Head(@).account,
                                                amount: Head(@).amount - least.amount,
                                                exchrate: Head(@).exchrate
                                            ], 
                                            Tail(@)
                                        )]
                                    /\ accounts' = [accounts EXCEPT 
                                        ![limitStrong.account][strong] = [
                                            balance: @.balance - strikeStrongAmount,
                                            \* Balance positions such that limit and loss sequences sum
                                            \* the balance of coin in the account
                                            positions: Balance(strong, @.balance - strikeStrongAmount, @.positions)
                                        ],
                                        ![limitStrong.account][weak] = [
                                            balance: @.balance + strikeWeakAmount
                                        ],
                                        ![weakStop.account][weak] = [
                                            balance: @.balance - strikeStrongAmount,
                                            \* Balance positions such that limit and loss sequences sum
                                            \* the balance of coin in the account
                                            positions: Balance(weak, @.balance - strikeStrongAmount, @.positions)
                                        ]
                                       ]
                            ELSE    /\ limits' = [limits EXCEPT ![p][strong] = Append (
                                        [
                                            account: Head(@).account,
                                            amount: Head(@).amount - least.amount,
                                            exchrate: Head(@).exchrate
                                        ], 
                                        Tail(@)
                                       )]
                                    /\ stops' = [stops EXCEPT ![p][weak] = Tail(@)
                                    /\ accounts' = [accounts EXCEPT 
                                        ![limitStrong.account] =
                                        ![weakStop.account] = 
            [] OTHER -> ctl' = "Stable"

=============================================================================
\* Modification History
\* Last modified Fri Jul 16 23:21:29 CDT 2021 by Charles Dusek
\* Created Fri Jul 16 22:17:43 CDT 2021 by Charles Dusek
