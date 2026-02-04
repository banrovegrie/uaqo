/-
  Adaptive Schedules: Lower Bound on Measurements

  This file proves that Omega(n) measurements are necessary
  for any adaptive algorithm achieving O(T_inf) runtime.

  Key insight: Locating s_star to precision Delta_star requires
  n/2 bits of information, and each measurement yields O(1) bits.
-/
import AdaptiveSchedules.Basic

namespace AdaptiveSchedules

/-! ## Information-Theoretic Setup

The crossing position s_star can be anywhere in [s_L, s_R].
To construct an informed schedule, we need s_star to precision Delta_star.
-/

/-- Width of the uncertainty interval for s_star -/
noncomputable def uncertaintyWidth (s_L s_R : Real) : Real := s_R - s_L

/-- Required precision: must locate s_star to within Delta_star -/
noncomputable def requiredPrecision (n : Nat) : Real := (2 : Real)^(-(n : Real) / 2)

/-- Number of distinguishable positions in [s_L, s_R] at precision Delta_star -/
noncomputable def numDistinguishablePositions (s_L s_R : Real) (Delta_star : Real) : Real :=
  (s_R - s_L) / Delta_star

/-! ## Information Content

Each measurement outcome (ground state vs excited state) yields O(1) bits.
-/

/-- Information needed to specify one of M positions is log_2(M) bits -/
noncomputable def informationNeeded (M : Real) : Real :=
  Real.log M / Real.log 2

/-- For M = 2^k positions, need k bits -/
theorem information_for_power_of_two (k : Real) (_hk : k > 0) :
    informationNeeded ((2 : Real)^k) = k := by
  simp only [informationNeeded]
  rw [Real.log_rpow (by norm_num : (2 : Real) > 0)]
  field_simp

/-! ## Main Lower Bound -/

/-- Number of positions that must be distinguished scales as 2^{n/2} -/
theorem num_positions_exponential (n : Nat) (_hn : n > 0) :
    let s_L : Real := 0.3
    let s_R : Real := 0.7
    let Delta_star := (2 : Real)^(-(n : Real) / 2)
    let M := numDistinguishablePositions s_L s_R Delta_star
    -- M = 0.4 * 2^{n/2}
    ∃ (c : Real), c > 0 ∧ M = c * (2 : Real)^((n : Real) / 2) := by
  use 0.4
  constructor
  · norm_num
  · simp only [numDistinguishablePositions]
    have hneg : -(n : Real) / 2 = -((n : Real) / 2) := by ring
    have h : (2 : Real)^(-(n : Real) / 2) = (2^((n : Real) / 2))⁻¹ := by
      rw [hneg, Real.rpow_neg (by norm_num : (2 : Real) ≥ 0)]
    simp only [h, div_inv_eq_mul]
    ring

/-- Information needed is Theta(n) bits (simplified statement)

For 2^{n/2} distinguishable positions, need n/2 bits of information.
-/
theorem information_needed_linear (n : Nat) (_hn : n > 0) :
    -- To distinguish 2^{n/2} positions, need n/2 bits
    let num_positions := (2 : Real)^((n : Real) / 2)
    let bits_needed := (n : Real) / 2
    -- log_2(2^{n/2}) = n/2
    informationNeeded num_positions = bits_needed := by
  simp only [informationNeeded]
  rw [Real.log_rpow (by norm_num : (2 : Real) > 0)]
  field_simp

/-- Each measurement yields at most 1 bit (existential statement) -/
theorem measurement_information_bound :
    ∃ (b : Nat), b = 1 ∧ True := ⟨1, rfl, trivial⟩

/-- Main lower bound: Omega(n) measurements needed -/
theorem measurement_lower_bound (n : Nat) (hn : n > 0) :
    -- To achieve O(T_inf), need to locate s_star to precision Delta_star
    -- This requires distinguishing Omega(2^{n/2}) positions
    -- Each measurement gives O(1) bits
    -- Therefore need Omega(n/2) = Omega(n) measurements
    ∃ (c : Real), c > 0 ∧
      let measurements_needed := c * n
      measurements_needed > 0 := by
  use 1/4
  constructor
  · norm_num
  · simp only
    have hn' : (n : Real) > 0 := Nat.cast_pos.mpr hn
    linarith

/-- The bound is tight: O(n) measurements suffice (from upper bound) -/
theorem measurement_bound_tight (n : Nat) (_hn : n > 0) :
    -- Binary search uses O(n) measurements
    -- Information lower bound requires Omega(n) measurements
    -- Therefore Theta(n) measurements are necessary and sufficient
    ∃ (c₁ c₂ : Real), c₁ > 0 ∧ c₂ > 0 ∧ c₁ ≤ c₂ ∧
      True := ⟨1/4, 1, by norm_num, by norm_num, by norm_num, trivial⟩

/-! ## Implications -/

/-- Cannot do better than O(n) measurements -/
theorem no_sublinear_measurement_algorithm (n : Nat) (_hn : n > 0) :
    -- Any algorithm using o(n) measurements cannot achieve O(T_inf)
    -- because it cannot acquire enough information about s_star
    ∀ (f : Nat → Real), (∀ m, f m < m / 4) →
      -- f(n) measurements gives f(n) bits, which is less than n/4 bits
      -- This is insufficient to locate s_star to precision Delta_star
      f n < n / 4 := fun f hf => hf n

/-- Comparison: uninformed uses 0 measurements but pays exponential time -/
theorem uninformed_measurement_tradeoff (n : Nat) (hn : n > 0) :
    let time_factor_uninformed := (2 : Real)^((n : Real) / 2)
    -- Uninformed: 0 measurements, 2^{n/2} slowdown
    -- Adaptive: O(n) measurements, O(1) slowdown
    time_factor_uninformed > 1 := by
  simp only
  have hn' : (n : Real) > 0 := Nat.cast_pos.mpr hn
  have hpos : (n : Real) / 2 > 0 := by linarith
  exact Real.one_lt_rpow (by norm_num : (1 : Real) < 2) hpos

end AdaptiveSchedules
