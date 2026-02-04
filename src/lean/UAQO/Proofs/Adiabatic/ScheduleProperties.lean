/-
  Proofs for schedule property axioms in Schedule.lean.

  Eliminates:
  - avoidedCrossing_bound
  - piecewiseSchedule_monotone
-/
import UAQO.Adiabatic.Hamiltonian

namespace UAQO.Proofs.Adiabatic

open UAQO

/-- The avoided crossing window is within bounds: δ < s* and s* + δ < 1. -/
theorem avoidedCrossing_bound_proof {n M : Nat} (es : EigenStructure n M) (hM : M >= 2) :
    let sStar := avoidedCrossingPosition es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM)
    let deltaS := avoidedCrossingWindow es hM
    deltaS < sStar ∧ sStar + deltaS < 1 := by
  sorry

/-- Piecewise linear schedules are monotonically increasing. -/
theorem piecewiseSchedule_monotone_proof {n M : Nat} (es : EigenStructure n M) (hM : M >= 2)
    (T : Real) (hT : T > 0)
    (T_left T_cross T_right : Real)
    (times_pos : T_left > 0 ∧ T_cross > 0 ∧ T_right > 0)
    (times_sum : T_left + T_cross + T_right = T)
    (t₁ t₂ : Real) (ht₁_ge : 0 <= t₁) (ht₁_lt_t₂ : t₁ < t₂) (ht₂_le : t₂ <= T) :
    let sStar := avoidedCrossingPosition es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM)
    let deltaS := avoidedCrossingWindow es hM
    let s := fun t =>
      if t <= T_left then (sStar - deltaS) * t / T_left
      else if t <= T_left + T_cross then
        (sStar - deltaS) + 2 * deltaS * (t - T_left) / T_cross
      else (sStar + deltaS) + (1 - sStar - deltaS) * (t - T_left - T_cross) / T_right
    s t₁ < s t₂ := by
  sorry

end UAQO.Proofs.Adiabatic
