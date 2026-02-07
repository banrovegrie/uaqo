import CircumventingBarrier.Basic
import Std

namespace CircumventingBarrier

/-- Reduced rank-2 equation used in Proposition 6. -/
def rank2ReducedEq (alpha beta Delta x : Rat) : Prop :=
  1 - (alpha / Delta) * x + (beta / (Delta * Delta)) * x * x = 0

/-- Delta-free normalized quadratic form. -/
def rank2NormalizedEq (alpha beta y : Rat) : Prop :=
  1 - alpha * y + beta * y * y = 0

/--
Scaling identity for Proposition 6:
solving the reduced equation at `(Delta, x)` is equivalent to solving
the normalized equation at `y = x / Delta`.
-/
theorem rank2ReducedEq_iff_normalized (alpha beta Delta x : Rat)
    (hDelta : Delta != 0) :
    rank2ReducedEq alpha beta Delta x <->
    rank2NormalizedEq alpha beta (x / Delta) := by
  unfold rank2ReducedEq rank2NormalizedEq
  have hExpr :
      (1 - (alpha / Delta) * x + (beta / (Delta * Delta)) * x * x)
        = (1 - alpha * (x / Delta) + beta * (x / Delta) * (x / Delta)) := by
    field_simp [hDelta]
    ring
  constructor
  . intro h
    calc
      1 - alpha * (x / Delta) + beta * (x / Delta) * (x / Delta)
          = 1 - (alpha / Delta) * x + (beta / (Delta * Delta)) * x * x := by
              symm
              exact hExpr
      _ = 0 := h
  . intro h
    calc
      1 - (alpha / Delta) * x + (beta / (Delta * Delta)) * x * x
          = 1 - alpha * (x / Delta) + beta * (x / Delta) * (x / Delta) := hExpr
      _ = 0 := h

/--
Any reduced root has linear scaling `x = kappa * Delta` with
`kappa = x / Delta` Delta-independent.
-/
theorem rank2_root_has_linear_scaling (alpha beta Delta x : Rat)
    (hDelta : Delta != 0)
    (hRoot : rank2ReducedEq alpha beta Delta x) :
    exists kappa : Rat,
      x = kappa * Delta /\
      rank2NormalizedEq alpha beta kappa := by
  refine Exists.intro (x / Delta) ?_
  constructor
  . have hMul : (x / Delta) * Delta = x := by
      field_simp [hDelta]
    simpa [mul_comm] using hMul.symm
  . exact (rank2ReducedEq_iff_normalized alpha beta Delta x hDelta).1 hRoot

/--
Conversely, any normalized root generates a reduced root by `x = kappa * Delta`.
-/
theorem rank2_root_from_normalized (alpha beta Delta kappa : Rat)
    (hDelta : Delta != 0)
    (hNorm : rank2NormalizedEq alpha beta kappa) :
    rank2ReducedEq alpha beta Delta (kappa * Delta) := by
  have hDiv : (kappa * Delta) / Delta = kappa := by
    field_simp [hDelta]
  have hNormAtDiv : rank2NormalizedEq alpha beta ((kappa * Delta) / Delta) := by
    simpa [hDiv] using hNorm
  exact (rank2ReducedEq_iff_normalized alpha beta Delta (kappa * Delta) hDelta).2 hNormAtDiv

end CircumventingBarrier
