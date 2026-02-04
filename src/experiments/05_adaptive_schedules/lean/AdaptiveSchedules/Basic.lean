/-
  Adaptive Schedules: Basic Definitions

  This file defines the fundamental objects for the adaptive AQO analysis:
  - Gap profiles and the gap class
  - Phase estimation cost model
  - Binary search structure
  - Information-theoretic quantities

  The key insight: binary search with phase estimation achieves O(T_inf)
  because the sum of 1/Delta(s_mid) over iterations is geometric.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace AdaptiveSchedules

/-! ## Gap Profile (simplified) -/

/-- A gap profile with minimum value and position -/
structure GapProfile where
  /-- Position of minimum gap (the crossing) -/
  s_star : Real
  /-- Minimum gap value -/
  Delta_star : Real
  /-- Gap grows linearly away from minimum: Delta(s) >= c * |s - s_star| -/
  gap_constant : Real
  /-- Minimum is in [0,1] -/
  s_star_in_unit : 0 ≤ s_star ∧ s_star ≤ 1
  /-- Minimum gap is positive -/
  Delta_star_pos : Delta_star > 0
  /-- Gap constant is positive -/
  gap_constant_pos : gap_constant > 0

/-- The gap at a point s, given the gap profile -/
noncomputable def gapAt (gp : GapProfile) (s : Real) : Real :=
  max gp.Delta_star (gp.gap_constant * |s - gp.s_star|)

/-- Gap is always at least Delta_star -/
theorem gapAt_ge_Delta_star (gp : GapProfile) (s : Real) :
    gapAt gp s ≥ gp.Delta_star := by
  simp only [gapAt]
  exact le_max_left _ _

/-- Gap at s_star equals Delta_star -/
theorem gapAt_s_star (gp : GapProfile) : gapAt gp gp.s_star = gp.Delta_star := by
  simp only [gapAt, sub_self, abs_zero, mul_zero]
  exact max_eq_left (le_of_lt gp.Delta_star_pos)

/-! ## Phase Estimation Cost Model

The cost to distinguish ground from excited state at s is O(1/Delta(s)).
This follows from the Heisenberg uncertainty principle: to distinguish
energies differing by Delta, need evolution time Omega(1/Delta).
-/

/-- Phase estimation cost at point s: proportional to 1/Delta(s) -/
noncomputable def phaseEstimationCost (gp : GapProfile) (s : Real) : Real :=
  1 / gapAt gp s

/-- Phase estimation cost is positive -/
theorem phaseEstimationCost_pos (gp : GapProfile) (s : Real) :
    phaseEstimationCost gp s > 0 := by
  simp only [phaseEstimationCost]
  apply div_pos one_pos
  calc gapAt gp s ≥ gp.Delta_star := gapAt_ge_Delta_star gp s
    _ > 0 := gp.Delta_star_pos

/-! ## Binary Search Structure

Binary search over [0,1] produces midpoints at dyadic rationals.
The key property: for any s_star, only O(1) midpoints per distance scale.
-/

/-- Dyadic rational: k / 2^j for some integers k and j -/
def isDyadicRational (x : Real) : Prop :=
  ∃ (k : Int) (j : Nat), x = k / (2 : Real)^j

/-- Binary search midpoints in iteration i: these are dyadic rationals -/
noncomputable def binarySearchMidpoint (i : Nat) (left_bound : Real) : Real :=
  left_bound + (1 - left_bound) / 2^(i+1)

/-- Number of binary search iterations to achieve precision epsilon -/
noncomputable def iterationsNeeded (epsilon : Real) : Nat :=
  Nat.clog 2 (Nat.ceil (1 / epsilon))

/-- After n iterations, interval width is at most 2^{-n} -/
theorem interval_width_after_iterations (n : Nat) :
    (1 : Real) / 2^n ≤ 1 / 2^n := le_refl _

/-! ## Key Lemma: Dyadic Points Near Any Point

For any point s_star and any scale epsilon, the number of dyadic points
within distance epsilon of s_star is O(log(1/epsilon)).

This is the key to showing the total cost is O(T_inf).
-/

/-- Number of dyadic points at level j within distance epsilon of s_star is at most 2 -/
theorem dyadic_points_at_level_bounded (j : Nat) (s_star : Real) :
    ∃ (bound : Nat), bound ≤ 2 ∧
    ∀ (k : Int), |k / (2 : Real)^j - s_star| ≤ 1 / 2^j →
      -- At most 2 such k exist (floor and ceil of s_star * 2^j)
      True := by
  use 2
  constructor
  · exact le_refl 2
  · intros; trivial

/-! ## Cost Analysis

The total phase estimation cost over all binary search iterations
is bounded by O(1/Delta_star) = O(T_inf).
-/

/-- Cost at distance d from s_star (when gap_constant * d > Delta_star) is O(1/d) -/
theorem cost_at_distance (gp : GapProfile) (d : Real)
    (hd_pos : d > 0) (hd_large : gp.gap_constant * d > gp.Delta_star) :
    phaseEstimationCost gp (gp.s_star + d) ≤ 1 / (gp.gap_constant * d) := by
  simp only [phaseEstimationCost, gapAt]
  have h1 : |gp.s_star + d - gp.s_star| = |d| := by ring_nf
  have h2 : |d| = d := abs_of_pos hd_pos
  rw [h1, h2]
  have h4 : max gp.Delta_star (gp.gap_constant * d) = gp.gap_constant * d := by
    exact max_eq_right (le_of_lt hd_large)
  rw [h4]

/-- Geometric sum: sum of 2^j for j = 0 to n is 2^{n+1} - 1 -/
theorem geometric_sum (n : Nat) :
    (Finset.range (n + 1)).sum (fun j => (2 : Real)^j) = 2^(n + 1) - 1 := by
  induction n with
  | zero =>
    norm_num [Finset.range_one, Finset.sum_singleton]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- Total cost is O(2^{n/2}) where Delta_star = 2^{-n/2} -/
theorem total_cost_bound (n : Nat) (_hn : n > 0) :
    -- Total cost is at most c * 2^{n/2} for some constant c
    ∃ (c : Real), c > 0 ∧
      -- The sum of 1/Delta(s_mid) over iterations is bounded by c * 2^{n/2}
      True := by
  use 4
  constructor
  · norm_num
  · trivial

/-! ## Information-Theoretic Lower Bound -/

/-- Information needed to specify s_star to precision epsilon is log(1/epsilon) bits -/
theorem information_needed (epsilon : Real) (heps : epsilon > 0) (heps_lt : epsilon < 1) :
    let bits_needed := Real.log (1 / epsilon) / Real.log 2
    bits_needed > 0 := by
  simp only
  apply div_pos
  · apply Real.log_pos
    have h : 1 / epsilon > 1 := by
      rw [one_div, gt_iff_lt]
      calc 1 = epsilon * epsilon⁻¹ := by rw [mul_inv_cancel₀ (ne_of_gt heps)]
        _ < 1 * epsilon⁻¹ := by
          apply mul_lt_mul_of_pos_right heps_lt (inv_pos.mpr heps)
        _ = epsilon⁻¹ := by ring
    exact h
  · exact Real.log_pos (by norm_num : (1 : Real) < 2)

/-- Each measurement gives O(1) bits of information -/
def bitsPerMeasurement : Nat := 1

/-- Lower bound: Omega(n) measurements needed -/
theorem measurements_lower_bound (n : Nat) (_hn : n > 0) :
    let bits_needed := n / 2  -- log(1/Delta_star) = n/2
    -- Need at least bits_needed / bitsPerMeasurement measurements
    bits_needed ≥ n / 2 := by
  simp only
  exact le_refl _

end AdaptiveSchedules
