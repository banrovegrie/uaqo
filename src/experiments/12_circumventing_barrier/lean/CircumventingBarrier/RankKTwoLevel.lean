import CircumventingBarrier.Basic
import Std

namespace CircumventingBarrier

/-- Two-level A_1 value for fixed N, d0, and Delta. -/
def twoLevelA1 (N d0 : Nat) (Delta : Rat) : Rat :=
  ((N - d0 : Nat) : Rat) / ((N : Rat) * Delta)

/-- Branch formula from reduced rank-k determinant roots x = kappa * Delta. -/
def reducedBranch (kappa Delta : Rat) : Rat :=
  1 / (1 + kappa * Delta)

/-- Algebraic rewrite used in Proposition 6A. -/
def reducedBranchViaA1 (N d0 : Nat) (kappa A1 : Rat) : Rat :=
  A1 / (A1 + kappa * (((N - d0 : Nat) : Rat) / (N : Rat)))

/-- If A1 = (N-d0)/(N*Delta), the two branch formulas are equal. -/
theorem reducedBranch_rewrite_A1 (N d0 : Nat) (kappa Delta : Rat)
    (hN : (N : Rat) != 0) (hDelta : Delta != 0) :
    reducedBranch kappa Delta =
    reducedBranchViaA1 N d0 kappa (twoLevelA1 N d0 Delta) := by
  unfold reducedBranch reducedBranchViaA1 twoLevelA1
  field_simp [hN, hDelta]
  ring

/-- Branch is strictly non-constant in Delta for kappa > 0. -/
theorem reducedBranch_nonconstant_in_Delta (kappa Delta1 Delta2 : Rat)
    (hk : 0 < kappa) (h1 : 0 < Delta1) (h2 : 0 < Delta2)
    (hNe : Delta1 != Delta2) :
    reducedBranch kappa Delta1 != reducedBranch kappa Delta2 := by
  intro hEq
  have hDen1Pos : 0 < 1 + kappa * Delta1 := by
    have hMulPos : 0 < kappa * Delta1 := mul_pos hk h1
    linarith
  have hDen2Pos : 0 < 1 + kappa * Delta2 := by
    have hMulPos : 0 < kappa * Delta2 := mul_pos hk h2
    linarith
  have hDen1Ne : 1 + kappa * Delta1 != 0 := ne_of_gt hDen1Pos
  have hDen2Ne : 1 + kappa * Delta2 != 0 := ne_of_gt hDen2Pos
  have hCross : (1 + kappa * Delta2) = (1 + kappa * Delta1) := by
    have hCrossRaw := (div_eq_div_iff hDen1Ne hDen2Ne).1 hEq
    -- 1*(1+k*D2) = 1*(1+k*D1)
    simpa [mul_comm, mul_left_comm, mul_assoc] using hCrossRaw
  have hLin : kappa * Delta2 = kappa * Delta1 := by linarith
  have hkNe : kappa != 0 := by exact ne_of_gt hk
  have hDeltaEq : Delta2 = Delta1 := mul_left_cancel0 hkNe hLin
  exact hNe hDeltaEq.symm

end CircumventingBarrier
