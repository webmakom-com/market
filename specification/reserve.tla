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

(******)
(* Parameters voted by NOM holders *)
(* catio: collateralization ratio *)
(* flatio: flation ratio *)
Param == [catio: Real, flatio: Real]

Type == /\  bonds \in [Pair -> [Coin -> Amount]]
        /\  tokens \in [Pair -> Amount]
            (*****)
            (* Time is abstracted to a counter that increments *)
            (* during an “time” step. All other steps are time stuttering *)
        /\  time \in Nat
        /\  accounts \in {Account}
        /\  params \in [Coin -> Param] 


(* Deposit NOM into Reserve Account *)
Deposit(amt) == 

(* Withdraw NOM from Reserve Account *)
Withdraw(amt)

(* Burn denom and unbond NOM *)
Burn(user, denom) ==

(* Mint denom and bond NOM *)
Mint(denom) == 


