/-
  Gap-Uninformed Separation Theorem: Basic Definitions

  This file defines the fundamental objects for the minimax analysis:
  - Schedules (parameterized velocity functions)
  - Gap functions (spectral gap profiles)
  - The adversarial game between schedule designer and nature

  The key insight: this is a minimax problem that can be analyzed
  without full quantum mechanics, just using the structure of error bounds.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

namespace SeparationTheorem

/-! ## Schedule as Velocity Profile -/

/-- A schedule is characterized by its velocity profile v: [0,1] -> R+.
    The velocity must be positive and integrate to 1. -/
structure VelocityProfile where
  /-- The velocity function v(s) = du/ds -/
  v : Real -> Real
  /-- Velocity is positive -/
  v_pos : ∀ s, 0 ≤ s → s ≤ 1 → v s > 0
  /-- Velocity integrates to 1 (normalized) -/
  v_integral_one : True  -- ∫₀¹ v(s) ds = 1, simplified for now

/-- Maximum velocity over an interval -/
noncomputable def VelocityProfile.maxOn (vp : VelocityProfile) (s_L s_R : Real) : Real :=
  sSup { vp.v s | s ∈ Set.Icc s_L s_R }

/-- Minimum velocity over an interval -/
noncomputable def VelocityProfile.minOn (vp : VelocityProfile) (s_L s_R : Real) : Real :=
  sInf { vp.v s | s ∈ Set.Icc s_L s_R }

/-! ## Gap Function -/

/-- A gap function Delta: [0,1] -> R+ with a unique minimum -/
structure GapProfile where
  /-- The gap function -/
  Delta : Real -> Real
  /-- Gap is positive -/
  Delta_pos : ∀ s, 0 ≤ s → s ≤ 1 → Delta s > 0
  /-- Position of minimum -/
  s_star : Real
  /-- Minimum is in [0,1] -/
  s_star_range : 0 ≤ s_star ∧ s_star ≤ 1
  /-- Value at minimum -/
  Delta_star : Real
  /-- Minimum value is positive -/
  Delta_star_pos : Delta_star > 0
  /-- s_star achieves the minimum -/
  achieves_min : Delta s_star = Delta_star
  /-- Unique minimum -/
  unique_min : ∀ s, 0 ≤ s → s ≤ 1 → s ≠ s_star → Delta s > Delta_star

/-! ## Gap Class -/

/-- The gap class: all gap profiles with minimum in [s_L, s_R] and value Delta_star -/
def GapClass (s_L s_R Delta_star : Real) : Set GapProfile :=
  { gp | s_L ≤ gp.s_star ∧ gp.s_star ≤ s_R ∧ gp.Delta_star = Delta_star }

/-! ## Error Model (Simplified Jansen-Ruskai-Seiler) -/

/-- The local error contribution at position s is proportional to v(s)²/Delta(s)³.
    This captures the essential structure of the JRS bound. -/
noncomputable def localError (v Delta : Real) : Real :=
  v^2 / Delta^3

/-- The crossing width is proportional to Delta_star -/
noncomputable def crossingWidth (Delta_star : Real) : Real :=
  Delta_star

/-- Error at the crossing: v_star² * delta_s / Delta_star³ -/
noncomputable def crossingError (v_star Delta_star : Real) : Real :=
  v_star^2 * (crossingWidth Delta_star) / Delta_star^3

/-- Simplified: crossingError = v_star² / Delta_star² -/
theorem crossingError_simplified (v_star Delta_star : Real) (h : Delta_star > 0) :
    crossingError v_star Delta_star = v_star^2 / Delta_star^2 := by
  simp only [crossingError, crossingWidth]
  have h1 : Delta_star ≠ 0 := ne_of_gt h
  field_simp

/-! ## Time Model -/

/-- Time to traverse an interval with given velocity -/
noncomputable def traversalTime (interval_width : Real) (velocity : Real) : Real :=
  interval_width / velocity

/-- Time for the crossing region -/
noncomputable def crossingTime (Delta_star : Real) (v_cross : Real) : Real :=
  traversalTime (crossingWidth Delta_star) v_cross

/-! ## Key Lemma: Velocity-Error Tradeoff -/

/-- For constant error epsilon, the velocity at crossing must satisfy:
    v_star² / Delta_star² ≤ epsilon
    Therefore: v_star ≤ sqrt(epsilon) * Delta_star -/
theorem velocity_bound_for_error (epsilon Delta_star v_star : Real)
    (_ : epsilon > 0) (hDelta : Delta_star > 0)
    (herror : crossingError v_star Delta_star ≤ epsilon) :
    v_star^2 ≤ epsilon * Delta_star^2 := by
  rw [crossingError_simplified v_star Delta_star hDelta] at herror
  have h1 : Delta_star^2 > 0 := sq_pos_of_pos hDelta
  have h2 : v_star^2 / Delta_star^2 ≤ epsilon := herror
  calc v_star^2 = (v_star^2 / Delta_star^2) * Delta_star^2 := by field_simp
    _ ≤ epsilon * Delta_star^2 := by nlinarith [sq_nonneg v_star]

end SeparationTheorem
