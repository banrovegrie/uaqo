/-
  Measure Condition: Basic Definitions

  This file defines the fundamental objects for the measure condition analysis:
  - Gap functions with flatness exponent alpha
  - The runtime exponent formula
  - Key scaling relationships

  The key insight: gap geometry (flatness exponent alpha) determines
  the runtime scaling T = Theta(1/Delta_star^{3 - 2/alpha}).
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

namespace MeasureCondition

/-! ## Gap Function with Flatness Exponent

A gap function with flatness exponent alpha near minimum:
  Delta(s) = Delta_star + c * |s - s_star|^alpha

where:
- Delta_star > 0 is the minimum gap
- c > 0 is a shape constant
- alpha > 0 is the flatness exponent
- s_star in [0,1] is the location of minimum
-/

/-- Parameters defining a gap function with power-law behavior near minimum -/
structure GapParams where
  /-- Minimum gap value -/
  Delta_star : Real
  /-- Minimum gap is positive -/
  hDelta_pos : Delta_star > 0
  /-- Shape constant -/
  c : Real
  /-- Shape constant is positive -/
  hc_pos : c > 0
  /-- Flatness exponent -/
  alpha : Real
  /-- Flatness exponent is positive -/
  halpha_pos : alpha > 0
  /-- Location of minimum -/
  s_star : Real
  /-- Minimum is in [0,1] -/
  hs_star_range : 0 ≤ s_star ∧ s_star ≤ 1

/-- The gap function: Delta(s) = Delta_star + c * |s - s_star|^alpha -/
noncomputable def gapFunction (p : GapParams) (s : Real) : Real :=
  p.Delta_star + p.c * |s - p.s_star| ^ p.alpha

/-- Gap function is positive everywhere -/
theorem gap_pos (p : GapParams) (s : Real) : gapFunction p s > 0 := by
  simp only [gapFunction]
  have h1 : p.c * |s - p.s_star| ^ p.alpha ≥ 0 := by
    apply mul_nonneg (le_of_lt p.hc_pos)
    exact Real.rpow_nonneg (abs_nonneg _) p.alpha
  calc p.Delta_star + p.c * |s - p.s_star| ^ p.alpha
    ≥ p.Delta_star + 0 := by linarith
    _ = p.Delta_star := by ring
    _ > 0 := p.hDelta_pos

/-- Gap achieves minimum at s_star -/
theorem gap_achieves_min (p : GapParams) : gapFunction p p.s_star = p.Delta_star := by
  simp only [gapFunction]
  have h : |p.s_star - p.s_star| = 0 := by simp
  rw [h, Real.zero_rpow (ne_of_gt p.halpha_pos), mul_zero, add_zero]

/-- Gap is strictly greater than minimum away from s_star -/
theorem gap_strictly_greater (p : GapParams) (s : Real) (hne : s ≠ p.s_star) :
    gapFunction p s > p.Delta_star := by
  simp only [gapFunction]
  have h1 : |s - p.s_star| > 0 := abs_pos.mpr (sub_ne_zero.mpr hne)
  have h2 : |s - p.s_star| ^ p.alpha > 0 := Real.rpow_pos_of_pos h1 p.alpha
  have h3 : p.c * |s - p.s_star| ^ p.alpha > 0 := mul_pos p.hc_pos h2
  linarith

/-! ## Sublevel Set Measure

For the gap function Delta(s) = Delta_star + c * |s - s_star|^alpha,
the sublevel set {s : Delta(s) <= x} for x = Delta_star + epsilon has:

  |s - s_star| <= (epsilon/c)^{1/alpha}

So the measure (length) near s_star is 2 * (epsilon/c)^{1/alpha}.

We define the key quantities without proving all the measure-theoretic details.
-/

/-- The radius of the sublevel set for gap value x = Delta_star + epsilon -/
noncomputable def sublevelRadius (p : GapParams) (epsilon : Real) : Real :=
  (epsilon / p.c) ^ (1 / p.alpha)

/-- The sublevel set measure (width of the interval) for x = Delta_star + epsilon -/
noncomputable def sublevelMeasure (p : GapParams) (epsilon : Real) : Real :=
  2 * sublevelRadius p epsilon

/-- Sublevel measure formula: mu = 2 * (epsilon/c)^{1/alpha} -/
theorem sublevel_measure_formula (p : GapParams) (epsilon : Real) :
    sublevelMeasure p epsilon = 2 * (epsilon / p.c) ^ (1 / p.alpha) := by
  simp only [sublevelMeasure, sublevelRadius]

/-! ## The Measure Condition

Definition (Guo-An 2025): A gap function Delta satisfies the measure condition if
there exists C > 0 such that for all x > 0:
  mu({s in [0,1] : Delta(s) <= x}) <= C * x

For our gap function with flatness exponent alpha, we analyze when this holds
with C independent of Delta_star.
-/

/-- The measure condition constant for threshold x = Delta_star + epsilon -/
noncomputable def measureRatio (p : GapParams) (epsilon : Real) : Real :=
  sublevelMeasure p epsilon / (p.Delta_star + epsilon)

/-! ## Runtime Scaling

The key result from power-law scheduling analysis:

With power-law scheduling u'(s) ~ Delta^p, the adiabatic error transforms to:
  eta ~ (1/T) * c_p * integral Delta^{p-3} ds

where c_p = integral Delta^{-p}.

Using gap integral bounds:
- c_p = Theta(Delta_star^{1/alpha - p})
- integral Delta^{-(3-p)} = Theta(Delta_star^{1/alpha + p - 3})
- Product = Theta(Delta_star^{2/alpha - 3})

For constant error: T = Theta(1/Delta_star^{3 - 2/alpha})
-/

/-- The runtime exponent: gamma = 3 - 2/alpha -/
noncomputable def runtimeExponent (alpha : Real) : Real :=
  3 - 2 / alpha

/-- For alpha = 1 (linear gap), runtime exponent is 1 -/
theorem runtime_exponent_linear : runtimeExponent 1 = 1 := by
  simp only [runtimeExponent]
  norm_num

/-- For alpha = 2 (quartic gap), runtime exponent is 2 -/
theorem runtime_exponent_quartic : runtimeExponent 2 = 2 := by
  simp only [runtimeExponent]
  norm_num

/-- For alpha = 3, runtime exponent is 7/3 -/
theorem runtime_exponent_cubic : runtimeExponent 3 = 7 / 3 := by
  simp only [runtimeExponent]
  norm_num

/-- For alpha = 1.5, runtime exponent is 5/3 -/
theorem runtime_exponent_1_5 : runtimeExponent 1.5 = 5 / 3 := by
  simp only [runtimeExponent]
  norm_num

/-- Runtime exponent is less than 3 for finite alpha -/
theorem runtime_exponent_lt_3 (alpha : Real) (halpha : alpha > 0) :
    runtimeExponent alpha < 3 := by
  simp only [runtimeExponent]
  have h : 2 / alpha > 0 := div_pos (by norm_num : (2 : Real) > 0) halpha
  linarith

/-- Runtime exponent equals 1 iff alpha = 1 -/
theorem runtime_exponent_eq_1_iff (alpha : Real) (halpha : alpha > 0) :
    runtimeExponent alpha = 1 ↔ alpha = 1 := by
  simp only [runtimeExponent]
  constructor
  · intro h
    have h1 : 3 - 2 / alpha = 1 := h
    have h2 : 2 / alpha = 2 := by linarith
    have halpha_ne : alpha ≠ 0 := ne_of_gt halpha
    field_simp at h2
    linarith
  · intro h
    rw [h]
    norm_num

/-- Runtime exponent is monotonically increasing in alpha -/
theorem runtime_exponent_strict_mono (alpha1 alpha2 : Real)
    (h1 : alpha1 > 0) (h2 : alpha2 > 0) (h12 : alpha1 < alpha2) :
    runtimeExponent alpha1 < runtimeExponent alpha2 := by
  simp only [runtimeExponent]
  -- Want: 3 - 2/alpha1 < 3 - 2/alpha2
  -- This is: 2/alpha2 < 2/alpha1
  -- Equivalent to: 2 * alpha1 < 2 * alpha2 (when both positive)
  have h1' : alpha1 ≠ 0 := ne_of_gt h1
  have h2' : alpha2 ≠ 0 := ne_of_gt h2
  have hp : alpha1 * alpha2 > 0 := mul_pos h1 h2
  have key : 2 / alpha2 < 2 / alpha1 := by
    have step1 : 2 * alpha1 < 2 * alpha2 := by linarith
    have step2 : 2 / alpha2 * (alpha1 * alpha2) = 2 * alpha1 := by field_simp
    have step3 : 2 / alpha1 * (alpha1 * alpha2) = 2 * alpha2 := by field_simp
    nlinarith
  linarith

/-- Runtime exponent >= 1 for alpha >= 1 -/
theorem runtime_exponent_ge_1 (alpha : Real) (halpha : alpha ≥ 1) :
    runtimeExponent alpha ≥ 1 := by
  simp only [runtimeExponent]
  have halpha_pos : alpha > 0 := by linarith
  have halpha_ne : alpha ≠ 0 := ne_of_gt halpha_pos
  have h : 2 / alpha ≤ 2 := by
    have step : 2 / alpha * alpha = 2 := by field_simp
    nlinarith
  linarith

/-- Runtime exponent < 1 for alpha < 1 -/
theorem runtime_exponent_lt_1 (alpha : Real) (halpha_pos : alpha > 0) (halpha : alpha < 1) :
    runtimeExponent alpha < 1 := by
  simp only [runtimeExponent]
  have halpha_ne : alpha ≠ 0 := ne_of_gt halpha_pos
  have h : 2 / alpha > 2 := by
    have step : 2 / alpha * alpha = 2 := by field_simp
    nlinarith
  linarith

/-! ## Measure Condition Characterization

The measure condition holds with C independent of Delta_star iff alpha <= 1.

Key insight: For x = 2*Delta_star, the measure ratio is
  2 * (Delta_star/c)^{1/alpha} / (2*Delta_star) = Delta_star^{1/alpha - 1} / c^{1/alpha}

- For alpha <= 1: exponent 1/alpha - 1 >= 0, so ratio bounded for Delta_star in (0,1]
- For alpha > 1: exponent 1/alpha - 1 < 0, so ratio -> infinity as Delta_star -> 0
-/

/-- The critical exponent for measure condition: 1/alpha - 1 -/
noncomputable def measureExponent (alpha : Real) : Real :=
  1 / alpha - 1

/-- Measure exponent >= 0 iff alpha <= 1 -/
theorem measure_exponent_nonneg_iff (alpha : Real) (halpha : alpha > 0) :
    measureExponent alpha ≥ 0 ↔ alpha ≤ 1 := by
  simp only [measureExponent]
  have halpha_ne : alpha ≠ 0 := ne_of_gt halpha
  constructor
  · intro h
    -- 1/alpha - 1 >= 0 means 1/alpha >= 1
    have h1 : 1 / alpha ≥ 1 := by linarith
    have step : 1 / alpha * alpha = 1 := by field_simp
    nlinarith
  · intro h
    -- alpha <= 1 means 1/alpha >= 1 means 1/alpha - 1 >= 0
    have step : 1 / alpha * alpha = 1 := by field_simp
    nlinarith

/-- Measure exponent < 0 iff alpha > 1 -/
theorem measure_exponent_neg_iff (alpha : Real) (halpha : alpha > 0) :
    measureExponent alpha < 0 ↔ alpha > 1 := by
  simp only [measureExponent]
  have halpha_ne : alpha ≠ 0 := ne_of_gt halpha
  constructor
  · intro h
    -- 1/alpha - 1 < 0 means 1/alpha < 1
    have h1 : 1 / alpha < 1 := by linarith
    have step : 1 / alpha * alpha = 1 := by field_simp
    nlinarith
  · intro h
    -- alpha > 1 means 1/alpha < 1 means 1/alpha - 1 < 0
    have step : 1 / alpha * alpha = 1 := by field_simp
    nlinarith

end MeasureCondition
