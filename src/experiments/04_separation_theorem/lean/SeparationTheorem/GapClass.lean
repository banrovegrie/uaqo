/-
  Gap-Uninformed Separation Theorem: Gap Class Definition

  The gap class G[s_L, s_R, Delta_*] contains all gap functions where:
  1. The minimum is at some s* in [s_L, s_R]
  2. The minimum value is Delta_*
  3. The measure condition holds (gap doesn't stay small too long)
-/
import SeparationTheorem.Basic

namespace SeparationTheorem

/-! ## Gap Class Definition -/

/-- The measure condition: mu({u : Delta(u) <= x}) <= C * x
    This ensures the gap doesn't remain small for too long. -/
def satisfiesMeasureCondition (gap : GapFunction) (C : Real) : Prop :=
  ∀ x > 0, MeasureTheory.volume { s : Real | s ∈ Set.Icc 0 1 ∧ gap.Delta s ≤ x } ≤
    ENNReal.ofReal (C * x)

/-- A gap function has a unique minimum in the interval [s_L, s_R] -/
def hasMinimumIn (gap : GapFunction) (s_L s_R : Real) : Prop :=
  ∃ s_star ∈ Set.Icc s_L s_R,
    gap.Delta s_star = gap.minGap ∧
    ∀ s ∈ Set.Icc 0 1, s ≠ s_star → gap.Delta s > gap.minGap

/-- The gap class G[s_L, s_R, Delta_*] -/
def GapClass (s_L s_R Delta_star : Real) (hs : s_L < s_R) (hDelta : Delta_star > 0) :
    Set GapFunction :=
  { gap | hasMinimumIn gap s_L s_R ∧
          gap.minGap = Delta_star ∧
          satisfiesMeasureCondition gap 2 }

/-! ## Properties of Gap Classes -/

/-- The gap class is non-empty for reasonable parameters -/
theorem gapClass_nonempty (s_L s_R Delta_star : Real)
    (hs : s_L < s_R) (hDelta : Delta_star > 0)
    (hs_L : 0 ≤ s_L) (hs_R : s_R ≤ 1) :
    (GapClass s_L s_R Delta_star hs hDelta).Nonempty := by
  sorry

/-- For any s* in [s_L, s_R], there exists a gap function with minimum at s* -/
theorem exists_gap_with_minimum_at (s_L s_R Delta_star s_star : Real)
    (hs : s_L < s_R) (hDelta : Delta_star > 0)
    (hs_star : s_star ∈ Set.Icc s_L s_R) :
    ∃ gap ∈ GapClass s_L s_R Delta_star hs hDelta,
      gap.minPosition = s_star := by
  sorry

/-! ## Crossing Width -/

/-- The crossing width delta_s is O(Delta_*) -/
noncomputable def crossingWidth (Delta_star : Real) : Real :=
  Delta_star  -- Simplified: delta_s = Theta(Delta_*)

/-- The crossing width is proportional to the minimum gap -/
theorem crossingWidth_prop (Delta_star : Real) (hDelta : Delta_star > 0) :
    ∃ C₁ C₂ : Real, C₁ > 0 ∧ C₂ > 0 ∧
      C₁ * Delta_star ≤ crossingWidth Delta_star ∧
      crossingWidth Delta_star ≤ C₂ * Delta_star := by
  use 1, 1
  simp [crossingWidth]
  constructor <;> linarith

end SeparationTheorem
