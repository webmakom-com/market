-—————————— MODULE reserve -——————————
EXTENDS     Naturals, Sequences, Reals

CONSTANT    Coin,   \* Set of all coins
            Pair   \* Set of all pairs of coins
           
VARIABLE    book,   \* Order Book
            bonds,  \* AMM Bond Curves
            
——————————————————————————
NoVal ==    CHOOSE v : v \notin Nat

Amount == r \in Real

(*****)
(* NOM is the representation of credit in the Onomy Reserve *)
(* Each account has a single balance of NOM with many *)
(* balances of minted Denoms *)
(* NOM: considered as Credits *)
(* Denoms: considered as Debits against the Credits *)
Account == [NOM: Amount, denoms: {[denom: Coin, amount: Amount]}]

Type == /\  bonds \in [Pair -> [Coin -> Amount]]
        /\  tokens \in [Pair -> Amount]
            (*****)
            (* You could think of this as time *)
            (* The issue is that time is not a thing *)
            (* In asynchronous environment *)
            (* will read up on real-time specs but for now *)
            (* abstract to counter *)
        /\  count \in Nat
        /\  accounts \in {Account}


(* Deposit NOM into Reserve Account *)
Deposit(amt) == 

(* Withdraw NOM from Reserve Account *)
Withdraw(amt)

(* Burn denom and unbond NOM *)
Burn(user, denom) ==

(* Mint denom and bond NOM *)
Mint(denom) == 


