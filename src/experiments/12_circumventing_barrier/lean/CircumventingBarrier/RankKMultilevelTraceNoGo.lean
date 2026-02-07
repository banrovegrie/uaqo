import CircumventingBarrier.RankKMultilevelCommuting
import Std

namespace CircumventingBarrier

/-- Sum of reciprocal reduced roots represented as a finite list. -/
def reciprocalRootSum (roots : List Rat) : Rat :=
  (roots.map (fun x => (1 : Rat) / x)).sum

/-- Reciprocal-root sum is invariant under permutation of the root list. -/
theorem reciprocalRootSum_perm {roots1 roots2 : List Rat}
    (hPerm : roots1.Perm roots2) :
    reciprocalRootSum roots1 = reciprocalRootSum roots2 := by
  unfold reciprocalRootSum
  exact (hPerm.map (fun x => (1 : Rat) / x)).sum_eq

/--
Proposition 6C core (trace no-go, list form):
if one varied gap contributes a positive trace weight, the profile
`const + coeff / Delta` changes across distinct positive gaps. Therefore two
instances with those gaps cannot have identical positive-root multisets
(represented here as permutation-equivalent root lists) while matching trace
identities via reciprocal root sums.
-/
theorem multilevel_trace_nogo_list_form
    (const coeff Delta1 Delta2 : Rat)
    (roots1 roots2 : List Rat)
    (hCoeff : 0 < coeff)
    (hDelta1 : 0 < Delta1) (hDelta2 : 0 < Delta2)
    (hNe : Delta1 != Delta2)
    (hTrace1 : reciprocalRootSum roots1 = singleGapProfile const coeff Delta1)
    (hTrace2 : reciprocalRootSum roots2 = singleGapProfile const coeff Delta2)
    (hPerm : roots1.Perm roots2) :
    False := by
  have hProfileNe :
      singleGapProfile const coeff Delta1 !=
      singleGapProfile const coeff Delta2 :=
    singleGapProfile_nonconstant const coeff Delta1 Delta2
      hCoeff hDelta1 hDelta2 hNe
  have hRecipEq : reciprocalRootSum roots1 = reciprocalRootSum roots2 :=
    reciprocalRootSum_perm hPerm
  have hProfileEq :
      singleGapProfile const coeff Delta1 =
      singleGapProfile const coeff Delta2 := by
    calc
      singleGapProfile const coeff Delta1 = reciprocalRootSum roots1 := by
        symm
        exact hTrace1
      _ = reciprocalRootSum roots2 := hRecipEq
      _ = singleGapProfile const coeff Delta2 := hTrace2
  exact hProfileNe hProfileEq

end CircumventingBarrier
