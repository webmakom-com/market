-—————————— MODULE market -——————————
EXTENDS     Naturals, Sequences, Reals

CONSTANT    Coin,   \* Set of all coins
            Pair   \* Set of all pairs of coins
           
VARIABLE    book,   \* Order Book
            bonds,  \* AMM Bond Curves
            
——————————————————————————
NoVal ==    CHOOSE v : v \notin Nat

Type == /\  bonds \in [Pair -> [Coin -> Amount]]
        /\  tokens \in [Pair -> Amount]

Mint(denom) ==


