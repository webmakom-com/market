-—————————— MODULE reserve -——————————
EXTENDS     Naturals, Sequences, Reals

CONSTANT    Coin,   \* Set of all coins
            Pair   \* Set of all pairs of coins
           
VARIABLE    book,   \* Order Book
            bonds,  \* AMM Bond Curves
            
——————————————————————————
NoVal ==    CHOOSE v : v \notin Nat

Type == /\  bonds \in [Pair -> [Coin -> Amount]]
        /\  tokens \in [Pair -> Amount]

(* Deposit NOM into Reserve Account *)
Deposit(user) == 

(* Burn denom to unbond NOM *)
Burn(user, denom) ==

(* Mint denom *)
Mint(denom) == 


