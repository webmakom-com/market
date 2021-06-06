------------------------------- MODULE reserve -------------------------------
EXTENDS     Naturals, Sequences, Reals

CONSTANT    Denom,  \* Set of all denoms
            Pair,   \* Set of all pairs of coins
            (* User constant is used to limit number of account records.   *)
            User    \* Set of all users
           
VARIABLE    book,   \* Order Book
            bonds   \* AMM Bond Curves
            
-----------------------------------------------------------------------------
NoVal ==    CHOOSE v : v \notin Nat

Amount == r \in Real

Inflation == r \in Real

(***************************************************************************)
(* Denoms are cryptocurrencies of whose exchange rate is stabilized against*)
(* a nationalized currency through the Onomy Reserve collateral management *)
(* system.                                                                 *)
(***************************************************************************)
Denom == [denom: Denom, amount: Real]

(***************************************************************************)
(* NOM coupons are redeemable for NOM by the reserve given they are        *)
(* surrendered with the proporional amount of denoms that are outstanding  *)
(*                                                                         *)
(* The coupon is denominated in NOM and the surrendered denoms are burned  *)
(*                                                                         *)
(* The goal of this feature is to allow for monetization of reserve        *) 
(* rewards without liquidating NOM collateral. It also allows others than  *)
(* the account holder to swap the basket index of currencies for NOM       *)
(* given they surrender the amount of swaps corresponding to the amount of *)
(* NOM redeemed                                                            *)
(*                                                                         *)
(* This "coupon" of stripped NOM bond that acts as a NOM put against the   *) 
(* denom or basket of denoms minted inflationary coupon rate.  The rate is *)
(* is a global function of percentage of the total NOM supply utilized as  *)
(* denom collateral bonded to the Onomy Reserve.                           *)
(***************************************************************************)
Coupon ==   [
                user: User, 
                amount: Real, 
                denoms: {[denom: Denom, amount: Amount]}
            ]

(***************************************************************************)
(* Swap from one currency to another.                                      *)
(*                                                                         *)
(* Swaps are created by depositing denoms into the Onomy Reserve and are   *)
(* priced by the user that creates them in the denom of their choice.      *)                                                      *)
(*                                                                         *)
(* The creating user must specify an expiration date upon which the denoms *)
(* are returned to the user and the swap is no longer valid.               *)
(*                                                                         *)
(* A Forward may be represented by a Swap with the same ask and bid denom. *)
(***************************************************************************)
Swap == [
            askDenom: Denom, 
            bidDenom: Denom, 
            amountAsk: Real, 
            exchrate: Real
        ]

(***************************************************************************)
(* The NOM coin is the representation of credit or a right to mint         *)
(* by the Onomy Reserve.                                                   *)
(*                                                                         *)
(* Each user account has a single balance of NOM with potential for many   *)
(* balances of denoms and coupons that they may or may not have minted.    *)
(***************************************************************************)
Account == [
    nom: Amount, 
    denoms: [Denom -> Amount],
    coupons: {Coupon}
]

(***************************************************************************)
(* The Onomy Reserve                                                       *)
(*                                                                         *)
(* This Global Reserve holds the NOM collateral for all denoms minted as   *)
(* well as Denoms bonded to Swaps                                          *)
(***************************************************************************)
Reserve == [
    nom: Amount,
    denoms: {[denom: Denom, amount: Real]}
]

(***************************************************************************)
(* Denom Specific Parameters voted by NOM holders                          *)
(*                                                                         *)
(* catio: minimum minting collateralization ratio (denom specific)         *)
(* latio: liquidation collateralization ratio (denom specific)             *)
(* destatio: percentage of denom staked at validator (denom specific)      *)
(***************************************************************************)
DeParam == [catio: Real, destatio: Real, flatio: Real]



Type == /\  coupons \in [User -> Token]
        /\  deparams \in [Denom -> DeParam]
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

(***************************************************************************)
(* Credit NOM to User Account. Add r to balance.                           *)
(***************************************************************************)
Deposit(user) ==  /\ \E r \in Reals :
                        /\ accounts' = [accounts EXCEPT ![user].nom = @ + r]
                        /\ UNCHANGED << bonds, tokens, time, params >>
(***************************************************************************)
(* Debit NOM from User Account. Sub r from balance.                        *)
(***************************************************************************)
Withdraw(user) == /\ \E r \in Reals : 
                        /\ r < account[user].nom
                        /\ accounts' = [accounts EXCEPT ![user].nom = @ - r]
                        /\ UNCHANGED << bonds, tokens, time, params >>

(* Mint denom and bond NOM *)
Mint(user) ==  
    LET nomBal == accounts[user].nom
    IN 
        (*********************** Qualifying Condition **********************)
        (* Nom balance of user account greater than 0                      *)
        (*******************************************************************)
        /\ nomBal > 0
        (*******************************************************************)
        (* There exists r in Reals such that : r is less than the user     *)
        (* account nom balance                                             *)
        (*******************************************************************)
        /\ \E r \in Reals : 
            /\ r < nomBal
            /\ accounts' = [accounts EXCEPT ![user].nom = @ - r]
            /\ reserve' = reserve + r
            (***************************************************************)
            (* Choose denom in denoms, will extend this to more than one   *)
            (***************************************************************)
            /\  LET desub == CHOOSE desub \in SUBSET Denom : TRUE
                IN 
                    LET F[d \in SUBSET desub] ==
                        IF d = {} THEN {} ELSE

    
(***************************************************************************)
(* Burn denom and unbond NOM                                               *)
(*                                                                         *)
(* Burning Denoms is like a past time, it’s fun.  Users really like doing  *)
(* it because it allows them to unlock their NOM, which they want to stake *)
(* with validators rather than mint Denoms.                                *)                         
(***************************************************************************)
Burn(user) ==   (* If there are coupons in the user's account, then choose *)
                (* a coupon that the user has enough denoms to redeem a    *)
                (* proportional amount of the coupon for NOM.              *)
                (***********************************************************)
                /\  coupons[user] # {}
                /\  LET coupon == 
                            CHOOSE coupon \in coupons[user] :
                                \A denom \in coupon.denoms : 
                                account[user].denoms[denom].amount # {}
                    IN
                        minDenom ==
                            CHOOSE 
                                min \in coupon.denoms : 
                                \A other \in coupon.denoms : 
                                min.amount <= y.amount
                    IN
                        LET burnBasis == \E r \in Real : r < minDenom
                        IN
                              /\ accounts’ = [accounts EXCEPT ![user].denoms =
                              
                                    
