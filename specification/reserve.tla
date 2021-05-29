-—————————— MODULE reserve -——————————
EXTENDS     Naturals, Sequences, Reals

CONSTANT    Coin,   \* Set of all coins
            Pair   \* Set of all pairs of coins
           
VARIABLE    book,   \* Order Book
            bonds,  \* AMM Bond Curves
            
——————————————————————————
NoVal ==    CHOOSE v : v \notin Nat

Type == /\  bonds \in [Pair -> [Coin -> Real]]
        /\  tokens \in [Pair -> Real]
            (*****)
            (* You could think of this as time *)
            (* The issue is that time is not a thing *)
            (* In asynchronous environment *)
            (* will read up on real-time specs*)
        /\  count in\ Nat


(* Deposit NOM into Reserve Account *)
Deposit(amt) == 

(* Withdraw NOM from Reserve Account *)
Withdraw(amt)

(* Burn denom and unbond NOM *)
Burn(user, denom) ==

(* Mint denom and bond NOM *)
Mint(denom) == 


