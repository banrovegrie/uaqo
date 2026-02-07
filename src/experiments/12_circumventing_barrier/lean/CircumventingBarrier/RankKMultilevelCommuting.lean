import CircumventingBarrier.Basic
import CircumventingBarrier.NoGo
import Std

namespace CircumventingBarrier

/-- Single-variable profile appearing when one level gap varies and others are fixed. -/
def singleGapProfile (const coeff Delta : Rat) : Rat :=
  const + coeff / Delta

/-- Branch map in the commuting multilevel reduction. -/
def commutingMultilevelBranch (const coeff Delta : Rat) : Rat :=
  crossingPosition (singleGapProfile const coeff Delta)

/-- Distinct positive gaps give distinct single-variable profiles for positive coefficient. -/
theorem singleGapProfile_nonconstant (const coeff Delta1 Delta2 : Rat)
    (hCoeff : 0 < coeff) (hDelta1 : 0 < Delta1) (hDelta2 : 0 < Delta2)
    (hNe : Delta1 != Delta2) :
    singleGapProfile const coeff Delta1 != singleGapProfile const coeff Delta2 := by
  intro hEq
  have hDivEq : coeff / Delta1 = coeff / Delta2 := add_left_cancel hEq
  have hDelta1Ne : Delta1 != 0 := ne_of_gt hDelta1
  have hDelta2Ne : Delta2 != 0 := ne_of_gt hDelta2
  have hCross : coeff * Delta2 = coeff * Delta1 := by
    exact (div_eq_div_iff hDelta1Ne hDelta2Ne).1 hDivEq
  have hCoeffNe : coeff != 0 := ne_of_gt hCoeff
  have hDeltaEq : Delta2 = Delta1 := mul_left_cancel0 hCoeffNe hCross
  exact hNe hDeltaEq.symm

/-- Commuting multilevel branch is non-constant in any varied supported gap. -/
theorem commutingBranch_nonconstant_in_Delta (const coeff Delta1 Delta2 : Rat)
    (hConst : 0 <= const) (hCoeff : 0 < coeff)
    (hDelta1 : 0 < Delta1) (hDelta2 : 0 < Delta2)
    (hNe : Delta1 != Delta2) :
    commutingMultilevelBranch const coeff Delta1 !=
    commutingMultilevelBranch const coeff Delta2 := by
  have hA1Ne : singleGapProfile const coeff Delta1 != singleGapProfile const coeff Delta2 :=
    singleGapProfile_nonconstant const coeff Delta1 Delta2 hCoeff hDelta1 hDelta2 hNe
  have hTerm1 : 0 < coeff / Delta1 := div_pos hCoeff hDelta1
  have hTerm2 : 0 < coeff / Delta2 := div_pos hCoeff hDelta2
  have hA1Pos1 : 0 < singleGapProfile const coeff Delta1 := by
    unfold singleGapProfile
    linarith
  have hA1Pos2 : 0 < singleGapProfile const coeff Delta2 := by
    unfold singleGapProfile
    linarith
  unfold commutingMultilevelBranch
  exact crossingPosition_injective_pos
    (singleGapProfile const coeff Delta1)
    (singleGapProfile const coeff Delta2)
    hA1Pos1 hA1Pos2 hA1Ne

/-- Multilevel profile G(Delta) = sum_l mu_l / Delta_l. -/
def multilevelProfile {L : Nat} (mu Delta : Fin L -> Rat) : Rat :=
  Finset.univ.sum (fun l => mu l / Delta l)

/-- Replace one selected gap by a new value. -/
def replaceGap {L : Nat} (Delta : Fin L -> Rat) (j : Fin L) (x : Rat) : Fin L -> Rat :=
  fun l => if l = j then x else Delta l

/-- Contribution of fixed levels except the selected varying one. -/
def restProfile {L : Nat} (mu Delta : Fin L -> Rat) (j : Fin L) : Rat :=
  (Finset.univ.erase j).sum (fun l => mu l / Delta l)

/-- Splitting multilevel profile into fixed part plus selected varying component. -/
theorem multilevelProfile_replace {L : Nat} (mu Delta : Fin L -> Rat)
    (j : Fin L) (x : Rat) :
    multilevelProfile mu (replaceGap Delta j x) =
    restProfile mu Delta j + mu j / x := by
  classical
  unfold multilevelProfile replaceGap restProfile
  have hj : Membership.mem j (Finset.univ : Finset (Fin L)) := Finset.mem_univ j
  rw [Finset.sum_erase_add _ hj]
  simp [hj]

/-- Nonnegativity of the fixed-part profile when coefficients and gaps are nonnegative. -/
theorem restProfile_nonneg {L : Nat} (mu Delta : Fin L -> Rat) (j : Fin L)
    (hMu : forall l : Fin L, 0 <= mu l)
    (hDelta : forall l : Fin L, 0 < Delta l) :
    0 <= restProfile mu Delta j := by
  classical
  unfold restProfile
  exact Finset.sum_nonneg (fun l _hl => div_nonneg (hMu l) (le_of_lt (hDelta l)))

/--
Multilevel profile non-constancy (no crossing map):
if mu_j > 0 and only Delta_j changes, then G(Delta) changes.
-/
theorem multilevelProfile_nonconstant_component {L : Nat}
    (mu DeltaBase : Fin L -> Rat) (j : Fin L)
    (hMuPos : 0 < mu j)
    (Delta1 Delta2 : Rat)
    (hDelta1 : 0 < Delta1) (hDelta2 : 0 < Delta2)
    (hNe : Delta1 != Delta2) :
    multilevelProfile mu (replaceGap DeltaBase j Delta1) !=
    multilevelProfile mu (replaceGap DeltaBase j Delta2) := by
  let const : Rat := restProfile mu DeltaBase j
  have hCore :
      singleGapProfile const (mu j) Delta1 !=
      singleGapProfile const (mu j) Delta2 :=
    singleGapProfile_nonconstant const (mu j) Delta1 Delta2
      hMuPos hDelta1 hDelta2 hNe
  have hRew1 :
      multilevelProfile mu (replaceGap DeltaBase j Delta1) = const + mu j / Delta1 := by
    simpa [const] using multilevelProfile_replace mu DeltaBase j Delta1
  have hRew2 :
      multilevelProfile mu (replaceGap DeltaBase j Delta2) = const + mu j / Delta2 := by
    simpa [const] using multilevelProfile_replace mu DeltaBase j Delta2
  rw [hRew1, hRew2]
  simpa [singleGapProfile] using hCore

/--
Multilevel commuting non-constancy when varying one supported gap:
if mu_j > 0 and only Delta_j changes, the branch value changes.
-/
theorem multilevel_branch_nonconstant_component {L : Nat}
    (mu DeltaBase : Fin L -> Rat) (j : Fin L)
    (hMuNonneg : forall l : Fin L, 0 <= mu l)
    (hMuPos : 0 < mu j)
    (hDeltaBase : forall l : Fin L, 0 < DeltaBase l)
    (Delta1 Delta2 : Rat)
    (hDelta1 : 0 < Delta1) (hDelta2 : 0 < Delta2)
    (hNe : Delta1 != Delta2) :
    crossingPosition (multilevelProfile mu (replaceGap DeltaBase j Delta1)) !=
    crossingPosition (multilevelProfile mu (replaceGap DeltaBase j Delta2)) := by
  let const : Rat := restProfile mu DeltaBase j
  have hConst : 0 <= const := by
    simpa [const] using restProfile_nonneg mu DeltaBase j hMuNonneg hDeltaBase
  have hBranchNe :
      commutingMultilevelBranch const (mu j) Delta1 !=
      commutingMultilevelBranch const (mu j) Delta2 :=
    commutingBranch_nonconstant_in_Delta const (mu j) Delta1 Delta2
      hConst hMuPos hDelta1 hDelta2 hNe
  have hRew1 :
      multilevelProfile mu (replaceGap DeltaBase j Delta1) = const + mu j / Delta1 := by
    simpa [const] using multilevelProfile_replace mu DeltaBase j Delta1
  have hRew2 :
      multilevelProfile mu (replaceGap DeltaBase j Delta2) = const + mu j / Delta2 := by
    simpa [const] using multilevelProfile_replace mu DeltaBase j Delta2
  rw [hRew1, hRew2]
  simpa [commutingMultilevelBranch, singleGapProfile] using hBranchNe

end CircumventingBarrier
