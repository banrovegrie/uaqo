/-
  Partial Information Theorem: Basic Definitions

  This file defines the fundamental objects for the partial information analysis:
  - Precision in A_1 estimation
  - Uncertainty intervals
  - The interpolation framework
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace PartialInformation

/-! ## The Crossing Position Function -/

/-- The crossing position as a function of A_1: s* = A_1 / (A_1 + 1) -/
noncomputable def crossingPosition (A_1 : Real) : Real :=
  A_1 / (A_1 + 1)

/-- The crossing position is in (0, 1) for A_1 > 0 -/
theorem crossingPosition_range (A_1 : Real) (hA : A_1 > 0) :
    0 < crossingPosition A_1 ∧ crossingPosition A_1 < 1 := by
  constructor
  · -- 0 < A_1 / (A_1 + 1)
    unfold crossingPosition
    apply div_pos hA
    linarith
  · -- A_1 / (A_1 + 1) < 1
    unfold crossingPosition
    rw [div_lt_one (by linarith : A_1 + 1 > 0)]
    linarith

/-- The crossing position function has derivative 1/(x+1)^2.
    We prove this using HasDerivAt. -/
theorem hasDerivAt_crossingPosition (A_1 : Real) (hA : A_1 > -1) :
    HasDerivAt crossingPosition (1 / (A_1 + 1)^2) A_1 := by
  unfold crossingPosition
  have h1 : A_1 + 1 ≠ 0 := by linarith
  -- Use the quotient rule: d/dx[f/g] = (f'g - fg')/g^2
  -- Here f(x) = x, g(x) = x + 1, f' = 1, g' = 1
  -- Result: (1*(x+1) - x*1)/(x+1)^2 = 1/(x+1)^2
  have hf : HasDerivAt (fun x : Real => x) 1 A_1 := hasDerivAt_id A_1
  have hg : HasDerivAt (fun x : Real => x + 1) 1 A_1 :=
    (hasDerivAt_id A_1).add_const 1
  convert hf.div hg h1 using 1
  field_simp [h1]
  ring

/-- Derivative of crossing position: d(s*)/d(A_1) = 1/(A_1 + 1)^2 -/
theorem crossingPosition_deriv (A_1 : Real) (hA : A_1 > -1) :
    deriv crossingPosition A_1 = 1 / (A_1 + 1)^2 :=
  (hasDerivAt_crossingPosition A_1 hA).deriv

/-! ## Precision Propagation -/

/-- Precision propagation: the uncertainty in s* is bounded by
    the uncertainty in A_1 times the maximum derivative.

    By the mean value theorem, for f(x) = x/(x+1):
    |f(A_1_est) - f(A_1)| <= max|f'(xi)| * |A_1_est - A_1|

    where xi is between A_1 and A_1_est.
    Since f'(x) = 1/(x+1)^2 is decreasing, the maximum occurs at
    the smaller value, giving the bound.

    This lemma is stated as a definition capturing the bound relationship.
    The main interpolation theorems do not require this lemma directly;
    they use the uncertainty width and its relationship to delta_A1.
-/
noncomputable def precisionBound (A_1 epsilon : Real) : Real :=
  epsilon / (A_1 + 1)^2

/-- The precision bound is positive for positive inputs -/
theorem precisionBound_pos (A_1 epsilon : Real)
    (hA : A_1 > -1) (heps : epsilon > 0) :
    precisionBound A_1 epsilon > 0 := by
  unfold precisionBound
  apply div_pos heps
  apply sq_pos_of_pos
  linarith

/-! ## Uncertainty Interval -/

/-- The uncertainty interval width given precision epsilon -/
noncomputable def uncertaintyWidth (A_1 epsilon : Real) : Real :=
  2 * epsilon / (A_1 + 1)^2

/-- Uncertainty width is positive for positive epsilon and A_1 > -1 -/
theorem uncertaintyWidth_pos (A_1 epsilon : Real)
    (hA : A_1 > -1) (heps : epsilon > 0) :
    uncertaintyWidth A_1 epsilon > 0 := by
  unfold uncertaintyWidth
  apply div_pos
  · linarith
  · apply sq_pos_of_pos; linarith

/-- The uncertainty width equals twice the precision bound -/
theorem uncertaintyWidth_eq_two_precisionBound (A_1 epsilon : Real) :
    uncertaintyWidth A_1 epsilon = 2 * precisionBound A_1 epsilon := by
  unfold uncertaintyWidth precisionBound
  ring

/-! ## Required Precision -/

/-- The required precision for optimality: delta_A1 = 2 * sqrt(d_0 * A_2 / N) -/
noncomputable def requiredPrecision (d_0 A_2 N : Real) : Real :=
  2 * Real.sqrt (d_0 * A_2 / N)

/-- Required precision is positive for positive parameters -/
theorem requiredPrecision_pos (d_0 A_2 N : Real)
    (hd : d_0 > 0) (hA2 : A_2 > 0) (hN : N > 0) :
    requiredPrecision d_0 A_2 N > 0 := by
  unfold requiredPrecision
  apply mul_pos
  · norm_num
  · apply Real.sqrt_pos.mpr
    apply div_pos
    · apply mul_pos hd hA2
    · exact hN

/-! ## Crossing Width -/

/-- The crossing width: delta_s = 2 * sqrt(d_0 * A_2 / N) / (A_1 + 1)^2 -/
noncomputable def crossingWidth (d_0 A_2 N A_1 : Real) : Real :=
  2 * Real.sqrt (d_0 * A_2 / N) / (A_1 + 1)^2

/-- Relationship: requiredPrecision = (A_1 + 1)^2 * crossingWidth -/
theorem requiredPrecision_eq_scaled_crossingWidth (d_0 A_2 N A_1 : Real)
    (hA : A_1 > -1) :
    requiredPrecision d_0 A_2 N = (A_1 + 1)^2 * crossingWidth d_0 A_2 N A_1 := by
  unfold requiredPrecision crossingWidth
  have h1 : (A_1 + 1)^2 ≠ 0 := pow_ne_zero 2 (by linarith : A_1 + 1 ≠ 0)
  have h2 : A_1 + 1 ≠ 0 := by linarith
  field_simp [h1, h2]

/-! ## Time Formulas -/

/-- Informed time (optimal with perfect knowledge) -/
noncomputable def informedTime (delta_s Delta_star sqrtEps : Real) : Real :=
  delta_s / (sqrtEps * Delta_star)

/-- Uninformed time over an interval of width W -/
noncomputable def uninformedTime (W Delta_star sqrtEps : Real) : Real :=
  W / (sqrtEps * Delta_star)

/-- The time ratio for a given interval width -/
noncomputable def timeRatio (W delta_s : Real) : Real :=
  W / delta_s

/-- Time ratio equals W / delta_s -/
theorem timeRatio_formula (W delta_s Delta_star sqrtEps : Real)
    (hDelta : Delta_star > 0) (hEps : sqrtEps > 0) (hds : delta_s > 0) :
    uninformedTime W Delta_star sqrtEps / informedTime delta_s Delta_star sqrtEps =
      timeRatio W delta_s := by
  unfold uninformedTime informedTime timeRatio
  have h1 : sqrtEps * Delta_star ≠ 0 := by
    apply mul_ne_zero
    · exact ne_of_gt hEps
    · exact ne_of_gt hDelta
  have h2 : delta_s ≠ 0 := ne_of_gt hds
  field_simp [h1, h2]

end PartialInformation
