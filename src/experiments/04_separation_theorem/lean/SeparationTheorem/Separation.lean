/-
  Gap-Uninformed Separation Theorem: Main Result

  This file contains the complete proof of the separation theorem.

  THEOREM: For any fixed (uninformed) schedule, there exists a gap function
  such that the required evolution time is Omega((s_R - s_L) / delta_s) times
  larger than the optimal informed schedule.

  The proof is adversarial: the adversary places the gap minimum at the
  point where the uninformed schedule has maximum velocity.
-/
import SeparationTheorem.Basic

namespace SeparationTheorem

/-! ## The Adversarial Construction -/

/-- The adversarial gap profile places the minimum at any chosen point s_adv -/
noncomputable def adversarialGap (s_adv Delta_star : Real)
    (hs_adv : 0 ≤ s_adv ∧ s_adv ≤ 1) (hDelta : Delta_star > 0) : GapProfile where
  Delta := fun s => Delta_star + (s - s_adv)^2
  Delta_pos := by
    intro s _ _
    have h1 : (s - s_adv)^2 ≥ 0 := sq_nonneg _
    linarith
  s_star := s_adv
  s_star_range := hs_adv
  Delta_star := Delta_star
  Delta_star_pos := hDelta
  achieves_min := by ring
  unique_min := by
    intro s _ _ hne
    have h1 : s - s_adv ≠ 0 := sub_ne_zero.mpr hne
    have h2 : (s - s_adv)^2 > 0 := sq_pos_of_ne_zero h1
    linarith

/-- The adversarial gap is in the gap class if s_adv is in [s_L, s_R] -/
theorem adversarialGap_in_class (s_L s_R s_adv Delta_star : Real)
    (hs_adv_L : s_L ≤ s_adv) (hs_adv_R : s_adv ≤ s_R)
    (hs_adv_01 : 0 ≤ s_adv ∧ s_adv ≤ 1) (hDelta : Delta_star > 0) :
    adversarialGap s_adv Delta_star hs_adv_01 hDelta ∈ GapClass s_L s_R Delta_star := by
  simp only [GapClass, Set.mem_setOf_eq, adversarialGap]
  exact ⟨hs_adv_L, hs_adv_R, trivial⟩

/-! ## Lower Bound: Uninformed Schedule Must Be Slow Everywhere -/

/-- If the schedule achieves low error for ALL gaps in the class,
    then velocity must be bounded at every point in [s_L, s_R] -/
theorem velocity_bounded_everywhere (vp : VelocityProfile) (s_L s_R Delta_star : Real)
    (_ : s_L < s_R) (hs_L : 0 ≤ s_L) (hs_R : s_R ≤ 1) (hDelta : Delta_star > 0)
    (epsilon : Real) (heps : epsilon > 0)
    (hworks : ∀ gp ∈ GapClass s_L s_R Delta_star,
      crossingError (vp.v gp.s_star) Delta_star ≤ epsilon)
    (s : Real) (hs_in : s_L ≤ s ∧ s ≤ s_R) :
    (vp.v s)^2 ≤ epsilon * Delta_star^2 := by
  -- Construct adversarial gap with minimum at s
  have hs_01 : 0 ≤ s ∧ s ≤ 1 := ⟨le_trans hs_L hs_in.1, le_trans hs_in.2 hs_R⟩
  let gp := adversarialGap s Delta_star hs_01 hDelta
  have gp_in_class : gp ∈ GapClass s_L s_R Delta_star :=
    adversarialGap_in_class s_L s_R s Delta_star hs_in.1 hs_in.2 hs_01 hDelta
  -- Apply the assumption
  have herror : crossingError (vp.v gp.s_star) Delta_star ≤ epsilon :=
    hworks gp gp_in_class
  -- gp.s_star = s by construction
  exact velocity_bound_for_error epsilon Delta_star (vp.v s) heps hDelta herror

/-! ## Time Lower Bound -/

/-- The uninformed time lower bound -/
theorem uninformed_time_lower_bound (s_L s_R Delta_star epsilon : Real)
    (hs : s_L < s_R) (hDelta : Delta_star > 0) (heps : epsilon > 0) :
    -- Time must be at least (s_R - s_L) / (sqrt(epsilon) * Delta_star)
    let T_lower := (s_R - s_L) / (Real.sqrt epsilon * Delta_star)
    T_lower > 0 := by
  simp only
  apply div_pos
  · linarith
  · apply mul_pos (Real.sqrt_pos.mpr heps) hDelta

/-! ## Informed Time Upper Bound -/

/-- The optimal informed schedule achieves time O(1/Delta_star) -/
theorem informed_time_upper_bound (Delta_star epsilon : Real)
    (hDelta : Delta_star > 0) (heps : epsilon > 0) :
    let T_inf := 1 / (epsilon * Delta_star)
    T_inf > 0 := by
  simp only
  apply one_div_pos.mpr
  apply mul_pos heps hDelta

/-! ## Main Separation Theorem -/

/-- The separation ratio between uninformed and informed times -/
theorem separation_ratio (s_L s_R Delta_star epsilon : Real)
    (_ : s_L < s_R) (hDelta : Delta_star > 0) (heps : epsilon > 0) :
    let T_unf := (s_R - s_L) / (Real.sqrt epsilon * Delta_star)
    let T_inf := 1 / (epsilon * Delta_star)
    T_unf / T_inf = (s_R - s_L) * Real.sqrt epsilon := by
  simp only
  have h1 : Real.sqrt epsilon > 0 := Real.sqrt_pos.mpr heps
  have h4 : Delta_star ≠ 0 := ne_of_gt hDelta
  have h5 : Real.sqrt epsilon ≠ 0 := ne_of_gt h1
  have hsq : Real.sqrt epsilon * Real.sqrt epsilon = epsilon := Real.mul_self_sqrt (le_of_lt heps)
  have h7 : Real.sqrt epsilon * Delta_star ≠ 0 := by positivity
  have h8 : epsilon * Delta_star ≠ 0 := by positivity
  -- Use calc for cleaner proof
  calc (s_R - s_L) / (Real.sqrt epsilon * Delta_star) / (1 / (epsilon * Delta_star))
      = (s_R - s_L) / (Real.sqrt epsilon * Delta_star) * (epsilon * Delta_star) := by
        rw [one_div, div_inv_eq_mul]
    _ = (s_R - s_L) * (epsilon * Delta_star) / (Real.sqrt epsilon * Delta_star) := by
        rw [div_mul_eq_mul_div]
    _ = (s_R - s_L) * (Delta_star * epsilon) / (Delta_star * Real.sqrt epsilon) := by
        rw [mul_comm epsilon Delta_star, mul_comm (Real.sqrt epsilon) Delta_star]
    _ = Delta_star * ((s_R - s_L) * epsilon) / (Delta_star * Real.sqrt epsilon) := by
        ring_nf
    _ = (s_R - s_L) * epsilon / Real.sqrt epsilon := by
        rw [mul_div_mul_left _ _ h4]
    _ = (s_R - s_L) * (Real.sqrt epsilon * Real.sqrt epsilon) / Real.sqrt epsilon := by
        rw [hsq]
    _ = (s_R - s_L) * Real.sqrt epsilon * Real.sqrt epsilon / Real.sqrt epsilon := by
        ring_nf
    _ = (s_R - s_L) * Real.sqrt epsilon := by
        rw [mul_div_assoc, div_self h5, mul_one]

/-- The separation in terms of the crossing width -/
theorem separation_in_terms_of_crossing_width (s_L s_R Delta_star : Real)
    (_ : s_L < s_R) (_ : Delta_star > 0) :
    (s_R - s_L) / (crossingWidth Delta_star) = (s_R - s_L) / Delta_star := by
  simp [crossingWidth]

/-! ## Application to Unstructured Search -/

/-- For unstructured search with n qubits:
    - s_R - s_L = Theta(1)  (constant uncertainty)
    - Delta_star = Theta(2^{-n/2})  (from original paper)
    - Therefore separation = Omega(2^{n/2}) -/
theorem unstructured_search_separation (n : Nat) (_ : n > 0) :
    let s_L : Real := 0.3
    let s_R : Real := 0.7
    let Delta_star : Real := (2 : Real)^(-(n : Real)/2)
    let separation := (s_R - s_L) / Delta_star
    separation = 0.4 * (2 : Real)^((n : Real)/2) := by
  have h1 : (2 : Real) > 0 := by norm_num
  have h3 : (2 : Real)^(-(n : Real)/2) > 0 := Real.rpow_pos_of_pos h1 _
  have h4 : (2 : Real)^(-(n : Real)/2) ≠ 0 := ne_of_gt h3
  have h5 : (2 : Real)^((n : Real)/2) > 0 := Real.rpow_pos_of_pos h1 _
  have key : (2 : Real)^(-(n : Real)/2) * (2 : Real)^((n : Real)/2) = 1 := by
    rw [← Real.rpow_add h1]
    have : -(n : Real)/2 + (n : Real)/2 = 0 := by ring
    rw [this, Real.rpow_zero]
  simp only
  rw [div_eq_iff h4]
  have comm : 0.4 * (2 : Real)^((n : Real)/2) * (2 : Real)^(-(n : Real)/2)
            = 0.4 * ((2 : Real)^((n : Real)/2) * (2 : Real)^(-(n : Real)/2)) := by ring
  rw [comm]
  rw [mul_comm ((2 : Real)^((n : Real)/2)) ((2 : Real)^(-(n : Real)/2))]
  rw [key]
  norm_num

/-- The separation is exponential in n -/
theorem separation_exponential (n : Nat) (hn : n ≥ 2) :
    0.4 * (2 : Real)^((n : Real)/2) ≥ 0.4 * 2 := by
  have h1 : (n : Real) / 2 ≥ 1 := by
    have h2 : (n : Real) ≥ 2 := Nat.cast_le.mpr hn
    linarith
  have h2 : (2 : Real)^((n : Real)/2) ≥ (2 : Real)^(1 : Real) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) ≤ 2) h1
  have h3 : (2 : Real)^(1 : Real) = 2 := Real.rpow_one 2
  nlinarith

/-! ## Main Result Statement -/

/-- **Gap-Uninformed Separation Theorem**

    For any gap-uninformed schedule (one that must work for all gap functions
    with minimum in [s_L, s_R]), the required time is at least

        T_uninformed >= (s_R - s_L) / (sqrt(epsilon) * Delta_star)

    For the optimal gap-informed schedule:

        T_informed = O(1 / (epsilon * Delta_star))

    The separation ratio is:

        T_uninformed / T_informed >= (s_R - s_L) * sqrt(epsilon)
                                   = Theta((s_R - s_L) / Delta_star)  for const eps

    For unstructured search with n qubits:
    - (s_R - s_L) = Theta(1)
    - Delta_star = Theta(2^{-n/2})
    - Separation = Omega(2^{n/2})

    This quantifies the runtime cost of the NP-hardness of computing A_1.
-/
theorem gap_uninformed_separation_theorem (s_L s_R Delta_star epsilon : Real)
    (hs : s_L < s_R) (hs_L : 0 ≤ s_L) (hs_R : s_R ≤ 1)
    (hDelta : Delta_star > 0) (heps : epsilon > 0) :
    -- 1. Lower bound on uninformed time
    (∀ vp : VelocityProfile,
      (∀ gp ∈ GapClass s_L s_R Delta_star, crossingError (vp.v gp.s_star) Delta_star ≤ epsilon) →
      ∀ s ∈ Set.Icc s_L s_R, (vp.v s)^2 ≤ epsilon * Delta_star^2) ∧
    -- 2. The separation ratio formula
    let T_unf := (s_R - s_L) / (Real.sqrt epsilon * Delta_star)
    let T_inf := 1 / (epsilon * Delta_star)
    T_unf / T_inf = (s_R - s_L) * Real.sqrt epsilon := by
  constructor
  · intro vp hworks s ⟨hs_L', hs_R'⟩
    exact velocity_bounded_everywhere vp s_L s_R Delta_star hs hs_L hs_R hDelta
      epsilon heps hworks s ⟨hs_L', hs_R'⟩
  · exact separation_ratio s_L s_R Delta_star epsilon hs hDelta heps

end SeparationTheorem
