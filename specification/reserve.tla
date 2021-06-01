------------------------------- MODULE reserve -------------------------------
EXTENDS     Naturals, Sequences, Reals

CONSTANT    Coin,   \* Set of all coins
            Pair,   \* Set of all pairs of coins
            User,   \* Set of all users
           
VARIABLE    book,   \* Order Book
            bonds,  \* AMM Bond Curves
            
-----------------------------------------------------------------------------
NoVal ==    CHOOSE v : v \notin Nat

Amount == r \in Real

(***************************************************************************)
(* The NOM coin is the representation of credit or a right to mint         *)
(* by the Onomy Reserve                                                    *)
(*                                                                         *)
(* Each user account has a single balance of NOM with potential for many   *)
(* outstanding balances of minted Denoms                                   *)
(*                                                                         *)
(* NOM: Credit                                                             *)
(* Denoms: Debits                                                          *)
(***************************************************************************)
Account == [
    nom: Amount, 
    denoms: {[denom: Coin, amount: Amount]}
]

(***************************************************************************)
(* Denom Specific Parameters voted by NOM holders                          *)
(*                                                                         *)
(* catio: minimum minting collateralization ratio (denom specific)         *)
(* latio: liquidation collateralization ratio (denom specific)             *)
(* destatio: percentage of denom staked at validator (denom specific)      *)
(***************************************************************************)
DeParam == [denom: Coin, catio: Real, destatio: Real, flatio: Real]

(***************************************************************************)
(* Swaps are used as a tradable index of currencies held in a reserve      *)
(* account.                                                                *)
(*                                                                         *)
(* Swaps are tied to specific accounts but are not permissioned            *)
(*                                                                         *)
(* The token is denominated in NOM and is redeemable for NOM when          *)
(* surrenderd along with the proportional amount of indexed currencies.    *)
(*                                                                         *)
(* The goal of this feature is to allow for monetization of reserve        *) 
(* rewards without liquidating NOM collateral. It also allows others than  *)
(* the account holder to swap the basket index of currencies for nom       *)
(* given they surrender the amount of swaps corresponding to the amount of *)
(* NOM redeemed                                                            *)
(*                                                                         *)
(* A swap is effectively a NOM put against the basket of denoms minted by  *)
(* a account with an inflationary coupon rate controlled by percentage of  *) 
(* NOM supply variable.                                                    *)
(***************************************************************************)
Swap == [user: User, amount: Real, denoms: {[denom: Coin, amount: Amount]}]

Type == /\  bonds \in [Pair -> [Coin -> Amount]]
            (***************************************************************)
            (* Swaps are used as a tradable index of the basket of         *)
            (* currencies held in a reserve account.                       *)
            (*                                                             *)
            (* The token is denominated in NOM and is redeemable for NOM   *)
            (* when surrendererd along with the proportional amount of     *)
            (* indexed currencies.                                         *)
            (*                                                             *)
            (* The goal of this feature is to allow for monetization of    *)
            (* minting rewards without liquidating NOM.  It also allows    *)
            (* others than the initiator to swap the basket for nom given  *)
            (* they surrender a purchased token                            *)
            (*                                                             *)
            (* It would effectively be a NOM put against the basket of     *)
            (* denoms minted by the account with a coupon rate dictated    *)
            (* by the weighted average of flatios of the denoms indexed    *)
            (***************************************************************)
        /\  swaps \in [User -> Token]
            (***************************************************************)
            (* Time is abstracted to a counter that increments during a    *) 
            (* “time” step. All other steps are time stuttering            *)
            (*                                                             *)
            (* In blockchain this corresponds to the block                 *)
            (*                                                             *)
            (* In asynchronous DAG, like with Equity protocol,             *)
            (* recurring processes relying on time, such as inflation,     *)
            (* will be triggered by a timer ran on correct nodes.          *)
            (*                                                             *)
            (* Timestamps of recurring DAG process will be the average of  *)
            (* reported times by nodes for each recurring process          *)
            (***************************************************************)
        /\  time \in Real
        /\  accounts \in [User -> Account]
        /\  params \in [Coin -> Param]


(* Deposit NOM into Reserve Account *)
Deposit(user) ==    /\ \E r \in Reals :
                        /\ 'accounts = [accounts EXCEPT ![user] = @.nom + r]
                        /\ UNCHANGED << bonds, tokens, time, params >>

(* Withdraw NOM from Reserve Account *)
Withdraw(amt)

(* Burn denom and unbond NOM *)
Burn(user, denom) ==

(* Mint denom and bond NOM *)
Mint(denom) == 


