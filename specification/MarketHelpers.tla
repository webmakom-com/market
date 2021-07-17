--------------------------- MODULE MarketHelpers ---------------------------
EXTENDS     Naturals, Sequences, SequencesExt

\* Nat tuple (numerator/denominator) inequality helper functions
\* All equalities assume Natural increments
GT(a, b) ==     IF a[1]*b[2] > a[2]*b[1] THEN TRUE ELSE FALSE

GTE(a, b) ==    IF a[1]*b[2] >= a[2]*b[1] THEN TRUE ELSE FALSE 

LT(a, b) ==     IF a[1]*b[2] < a[2]*b[1] THEN TRUE ELSE FALSE

LTE(a, b) ==    IF a[1]*b[2] <= a[2]*b[1] THEN TRUE ELSE FALSE

\* This division needs
BondAskAmount(bondAskBal, bondBidBal, bidAmount) ==
    (bondAskBal * bidAmount) \div bondBidBal

(***************************************************************************)
(* Max amount that Bond pool may sell of ask coin without                  *)
(* executing the most adjacent order                                       *)
(*                                                                         *)
(* Expression origin:                                                      *)
(* bondAsk / bondBid = erate                                               *)
(* d(bondAsk)/d(bondBid) = d(erate)                                        *)
(* d(bondAsk)/d(bondBid) = d(bondAsk)/d(bondBid)                           *)
(* d(bondAsk) = d(bondBid) * d(bondAsk)/d(bondBid)                         *)
(* d(bondAsk) = d(bondBid) * d(erate)                                      *)
(*                                                                         *)
(* Integrate over bondAsk on lhs and bondBid & erate on rhs then           *)
(* substitute and simplify                                                 *)
(*                                                                         *)
(* MaxBondBid =                                                            *)
(*                                                                         *)
(* erate(intial) = bondAsk / bondBid                                       *)
(*                                                                         *)
(* MaxBondBid =                                                            *)
(* bondAsk(initial) -                                                      *)
(* bondBid(initial) ^ 2 * erate(final) ^ 2 /                               *)
(* [(bondAsk(initial)/bondBid(initial)]                                    *)
(***************************************************************************)
MaxBondBid(erateFinal, bondNumerator, bondDenominator) ==  
    \* MaxBondBid = 
    \* bondAsk(initial) - 
    \* bondBid(initial)^2 * erate(final) ^ 2 / 
    \* erate(initial)
    bondDenominator * ((erateFinal[0] * bondDenominator) \div (erateFinal[1] * bondNumerator)) - bondNumerator

=============================================================================
\* Modification History
\* Last modified Sat Jul 17 11:22:35 CDT 2021 by Charles Dusek
\* Created Sat Jul 17 11:19:23 CDT 2021 by Charles Dusek
