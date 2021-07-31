--------------------------- MODULE MarketHelpers ---------------------------
EXTENDS Naturals, Sequences, SequencesExt

\* Nat tuple (numerator/denominator) inequality helper functions
\* All equalities assume Natural increments
GT(a, b) ==     IF a[1]*b[2] > a[2]*b[1] THEN TRUE ELSE FALSE

GTE(a, b) ==    IF a[1]*b[2] >= a[2]*b[1] THEN TRUE ELSE FALSE 

LT(a, b) ==     IF a[1]*b[2] < a[2]*b[1] THEN TRUE ELSE FALSE

LTE(a, b) ==    IF a[1]*b[2] <= a[2]*b[1] THEN TRUE ELSE FALSE

\* Sequence Helpers
IGT(limitSeq, pos) == {i \in 0..Len(limitSeq): limitSeq[i].exchrate > pos.exchrate}
ILT(stopSeq, pos) == {i \in 0..Len(stopSeq): stopSeq[i].exchrate < pos.exchrate}

\* This division needs
poolAskAmount(poolAskBal, poolBidBal, bidAmount) ==
    (poolAskBal * bidAmount) \div poolBidBal

(***************************************************************************)
(* Max amount that pool may sell of ask coin without                       *)
(* executing the most adjacent order                                       *)
(*                                                                         *)
(* Expression origin:                                                      *)
(* poolAsk / poolBid = erate                                               *)
(* d(poolAsk)/d(poolBid) = d(erate)                                        *)
(* d(poolAsk)/d(poolBid) = d(poolAsk)/d(poolBid)                           *)
(* d(poolAsk) = d(poolBid) * d(poolAsk)/d(poolBid)                         *)
(* d(poolAsk) = d(poolBid) * d(erate)                                      *)
(*                                                                         *)
(* Integrate over poolAsk on lhs and poolBid & erate on rhs then           *)
(* substitute and simplify                                                 *)
(*                                                                         *)
(* MaxpoolBid =                                                            *)
(* poolBid(initial) *                                                      *)
(* erate(final) *                                                          *)
(* (2 - erate(final) / erate(initial)) -                                   *)
(* poolAsk(initial)                                                        *)
(***************************************************************************)
MaxPoolBid(erateFinal, poolNumerator, poolDenominator) ==  
    poolDenominator * 
    (
        (erateFinal[0] \ erateFinal[1]) *
        (
            2 - 
            (erateFinal[0] * poolDenominator) \
            (erateFinal[1] * poolNumerator)
        )
    ) - poolNumerator
    

Stronger(pair, pools) ==  CHOOSE c \in pair : pools[<<pair, c>>] <= pools[<<pair, pair \ {c}>>]

SumSeq(s) ==    LET F[i \in 0..Len(s)] ==
                    IF i = 0 THEN 0
                    ELSE s[i] + F[i-1]
                IN  F[Len(s)]
                


=============================================================================
\* Modification History
\* Last modified Sat Jul 31 13:50:37 CDT 2021 by Charles Dusek
\* Created Sat Jul 17 11:19:23 CDT 2021 by Charles Dusek
