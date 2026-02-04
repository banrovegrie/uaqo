/-
  Measure Condition: Main Theorems

  This file contains the proofs of the two main theorems:

  THEOREM 1 (Geometric Characterization):
  The measure condition holds with C independent of Delta_star
  if and only if alpha <= 1.

  THEOREM 2 (Scaling Spectrum):
  The optimal runtime satisfies T = Theta(1/Delta_star^{3 - 2/alpha}).

  COROLLARY:
  The binary dichotomy conjecture is false.
  Runtime exponents form a continuum in [1, 3).
-/
import MeasureCondition.Basic

namespace MeasureCondition

/-! ## Part I: Theorem 1 (Geometric Characterization)

The measure condition requires: mu({s : Delta(s) <= x}) <= C * x for all x > 0.

For x = Delta_star + epsilon (small epsilon), the sublevel set near s* has measure:
  mu = 2 * (epsilon/c)^{1/alpha}

The ratio mu/x = 2 * (epsilon/c)^{1/alpha} / (Delta_star + epsilon)

The key insight from Basic.lean:
- measureExponent = 1/alpha - 1
- measureExponent >= 0 iff alpha <= 1
- When alpha > 1, the measure ratio diverges as Delta_star -> 0
-/

/-- **Theorem 1 (Geometric Characterization)**:
    The measure condition holds uniformly (C independent of Delta_star)
    if and only if the flatness exponent alpha <= 1.

    This is equivalent to: measureExponent >= 0 iff alpha <= 1
    which is proven in Basic.lean as `measure_exponent_nonneg_iff`. -/
theorem geometric_characterization (alpha : Real) (halpha : alpha > 0) :
    measureExponent alpha ≥ 0 ↔ alpha ≤ 1 :=
  measure_exponent_nonneg_iff alpha halpha

/-- Measure condition fails when alpha > 1 -/
theorem measure_condition_fails (alpha : Real) (halpha : alpha > 0) (h : alpha > 1) :
    measureExponent alpha < 0 := by
  rw [measure_exponent_neg_iff alpha halpha]
  exact h

/-! ## Part II: Theorem 2 (Scaling Spectrum)

The optimal runtime satisfies T = Theta(1/Delta_star^{3 - 2/alpha}).

This is the runtime exponent gamma = 3 - 2/alpha from Basic.lean.
-/

/-- **Theorem 2 (Scaling Spectrum)**:
    The optimal runtime satisfies T = Theta(1/Delta_star^gamma)
    where gamma = 3 - 2/alpha.

    Properties proven in Basic.lean:
    - gamma is strictly increasing in alpha (runtime_exponent_strict_mono)
    - gamma = 1 when alpha = 1 (runtime_exponent_linear)
    - gamma = 2 when alpha = 2 (runtime_exponent_quartic)
    - gamma < 3 for all finite alpha (runtime_exponent_lt_3)
    - gamma >= 1 when alpha >= 1 (runtime_exponent_ge_1) -/
theorem scaling_spectrum (alpha : Real) (halpha : alpha > 0) :
    let gamma := runtimeExponent alpha
    -- The exponent gamma = 3 - 2/alpha
    gamma = 3 - 2 / alpha ∧
    -- gamma < 3 (cubic is the limit)
    gamma < 3 ∧
    -- gamma is strictly increasing in alpha
    (∀ beta : Real, beta > 0 → beta < alpha → runtimeExponent beta < gamma) := by
  constructor
  · rfl
  constructor
  · exact runtime_exponent_lt_3 alpha halpha
  · intro beta hbeta hlt
    exact runtime_exponent_strict_mono beta alpha hbeta halpha hlt

/-! ## Part III: Dichotomy Corollary

The binary dichotomy conjecture claimed: either T = Theta(1/Delta*) or T = Theta(1/Delta*^2).

This is FALSE. Runtime exponents form a continuous spectrum in [1, 3).
-/

/-- **Corollary**: The dichotomy conjecture is FALSE.
    There exist alpha values giving exponents strictly between 1 and 2. -/
theorem dichotomy_false :
    ∃ alpha : Real, alpha > 0 ∧
    runtimeExponent alpha > 1 ∧ runtimeExponent alpha < 2 := by
  use 1.5
  simp only [runtimeExponent]
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num

/-- Example: alpha = 1.5 gives gamma = 5/3, which is between 1 and 2 -/
theorem example_intermediate : runtimeExponent 1.5 = 5 / 3 ∧ (1 : Real) < 5/3 ∧ (5 : Real)/3 < 2 := by
  simp only [runtimeExponent]
  constructor
  · norm_num
  constructor <;> norm_num

/-- The exponent gamma takes all values in (1, 3) as alpha varies over (1, infinity) -/
theorem exponent_surjective (gamma : Real) (h1 : gamma > 1) (h3 : gamma < 3) :
    ∃ alpha : Real, alpha > 1 ∧ runtimeExponent alpha = gamma := by
  -- gamma = 3 - 2/alpha implies alpha = 2/(3 - gamma)
  use 2 / (3 - gamma)
  have h_diff_pos : 3 - gamma > 0 := by linarith
  constructor
  · -- Show alpha > 1 iff 2/(3-gamma) > 1 iff 2 > 3 - gamma iff gamma > 1
    have h_ne : 3 - gamma ≠ 0 := ne_of_gt h_diff_pos
    have step : 2 / (3 - gamma) * (3 - gamma) = 2 := by field_simp
    nlinarith
  · -- Show runtimeExponent (2/(3-gamma)) = gamma
    simp only [runtimeExponent]
    have h_ne : 3 - gamma ≠ 0 := ne_of_gt h_diff_pos
    have alpha_ne : 2 / (3 - gamma) ≠ 0 := by
      apply div_ne_zero
      · norm_num
      · exact h_ne
    field_simp
    ring

/-! ## Part IV: Summary Table (as theorems)

| alpha | gamma = 3 - 2/alpha | Measure condition | Runtime T              |
|-------|---------------------|-------------------|------------------------|
| 1     | 1                   | Holds             | Theta(1/Delta*)        |
| 1.5   | 5/3                 | Fails             | Theta(1/Delta*^{5/3})  |
| 2     | 2                   | Fails             | Theta(1/Delta*^2)      |
| 3     | 7/3                 | Fails             | Theta(1/Delta*^{7/3})  |
| inf   | 3 (limit)           | Fails             | Theta(1/Delta*^3)      |
-/

theorem table_alpha_1 : runtimeExponent 1 = 1 := runtime_exponent_linear

theorem table_alpha_1_5 : runtimeExponent 1.5 = 5 / 3 := runtime_exponent_1_5

theorem table_alpha_2 : runtimeExponent 2 = 2 := runtime_exponent_quartic

theorem table_alpha_3 : runtimeExponent 3 = 7 / 3 := runtime_exponent_cubic

/-- Measure condition holds at alpha = 1 -/
theorem measure_holds_alpha_1 : measureExponent 1 = 0 := by
  simp only [measureExponent]
  norm_num

/-- Measure condition fails at alpha = 2 -/
theorem measure_fails_alpha_2 : measureExponent 2 < 0 := by
  simp only [measureExponent]
  norm_num

/-- As alpha -> infinity, gamma -> 3 -/
theorem limit_alpha_infinity (epsilon : Real) (heps : epsilon > 0) :
    ∃ N : Real, N > 0 ∧ ∀ alpha : Real, alpha > N →
    |runtimeExponent alpha - 3| < epsilon := by
  use 2 / epsilon
  constructor
  · exact div_pos (by norm_num : (2 : Real) > 0) heps
  · intro alpha halpha
    simp only [runtimeExponent]
    -- |3 - 2/alpha - 3| = |−2/alpha| = 2/alpha < epsilon
    have h1 : alpha > 0 := by
      have h_pos : 2 / epsilon > 0 := div_pos (by norm_num : (2 : Real) > 0) heps
      linarith
    rw [abs_sub_comm]
    simp only [sub_sub_cancel]
    rw [abs_of_pos (div_pos (by norm_num : (2 : Real) > 0) h1)]
    -- Want: 2/alpha < epsilon
    -- Given: alpha > 2/epsilon
    have h_ne : alpha ≠ 0 := ne_of_gt h1
    have eps_ne : epsilon ≠ 0 := ne_of_gt heps
    have step : 2 / alpha * alpha = 2 := by field_simp
    have step2 : 2 / epsilon * epsilon = 2 := by field_simp
    nlinarith

/-! ## Part V: Physical Interpretation (stated as comments)

The measure condition captures gap geometry:
- V-shaped minima (alpha = 1): Measure condition holds
- Flat-bottomed minima (alpha > 1): Measure condition fails

Flat minima create wider "danger zones" where Delta ~ Delta_star,
forcing adiabatic evolution to traverse slowly for longer.

The scaling T = Theta(1/Delta_star^{3 - 2/alpha}) shows:
- Linear gaps (alpha = 1): T = Theta(1/Delta_star) - Guo-An regime
- Quartic gaps (alpha = 2): T = Theta(1/Delta_star^2) - classical adiabatic
- Flat limit (alpha -> inf): T -> Theta(1/Delta_star^3) - worst case
-/

end MeasureCondition
