/-
  Secular equation analysis for the adiabatic Hamiltonian.

  The eigenvalues of H(s) = -(1-s)|ψ₀⟩⟨ψ₀| + s·H_z satisfy the secular equation:
    1/(1-s) = (1/N) Σ_k d_k/(s·E_k - λ)

  This file analyzes the secular equation function F(s,λ) and its roots:
  - F is strictly increasing in λ on each interval between poles
  - There are exactly M roots (one per interval)
  - The ground state eigenvalue is the root in (-∞, s·E₀)
  - Near the avoided crossing s*, the gap has hyperbolic structure

  These results form the foundation for proving the 7 spectral gap bound axioms.

  Reference: Section 2.2 of arXiv:2411.05736
-/
import UAQO.Spectral.AdiabaticHamiltonian
import UAQO.Spectral.SpectralParameters
import UAQO.Proofs.Spectral.EigenvalueCondition

namespace UAQO.Proofs.Spectral.SecularEquation

open UAQO Finset

/-! ## The secular equation function -/

/-- The secular equation function F(s,λ) = (1/N) Σ_k d_k/(s·E_k - λ) - 1/(1-s).
    Eigenvalues of H(s) that are not degenerate eigenvalues of s·H_z satisfy F(s,λ) = 0. -/
noncomputable def secularFun {n M : Nat} (es : EigenStructure n M)
    (_hM : M > 0) (s : Real) (lambda : Real) : Real :=
  let N := (qubitDim n : Real)
  (1 / N) * Finset.sum Finset.univ (fun k : Fin M =>
    (es.degeneracies k : Real) / (s * es.eigenvalues k - lambda)) - 1 / (1 - s)

/-- The derivative of the secular function with respect to λ.
    ∂F/∂λ = (1/N) Σ_k d_k/(s·E_k - λ)² > 0 when λ ≠ s·E_k for all k. -/
noncomputable def secularFunDeriv {n M : Nat} (es : EigenStructure n M)
    (_hM : M > 0) (s : Real) (lambda : Real) : Real :=
  let N := (qubitDim n : Real)
  (1 / N) * Finset.sum Finset.univ (fun k : Fin M =>
    (es.degeneracies k : Real) / (s * es.eigenvalues k - lambda)^2)

/-! ## Positivity of the derivative -/

/-- Each term in the derivative sum is non-negative. -/
lemma secularFunDeriv_term_nonneg {n M : Nat} (es : EigenStructure n M)
    (s : Real) (lambda : Real) (k : Fin M) :
    (es.degeneracies k : Real) / (s * es.eigenvalues k - lambda)^2 ≥ 0 := by
  apply div_nonneg
  · exact Nat.cast_nonneg _
  · exact sq_nonneg _

/-- Each term in the derivative sum is strictly positive when λ ≠ s·E_k. -/
lemma secularFunDeriv_term_pos {n M : Nat} (es : EigenStructure n M)
    (s : Real) (lambda : Real) (k : Fin M)
    (hne : lambda ≠ s * es.eigenvalues k) :
    (es.degeneracies k : Real) / (s * es.eigenvalues k - lambda)^2 > 0 := by
  apply div_pos
  · exact Nat.cast_pos.mpr (es.deg_positive k)
  · apply sq_pos_of_ne_zero
    exact sub_ne_zero.mpr (Ne.symm hne)

/-- The derivative is non-negative everywhere it's defined. -/
theorem secularFunDeriv_nonneg {n M : Nat} (es : EigenStructure n M)
    (_hM : M > 0) (s : Real) (lambda : Real) :
    secularFunDeriv es _hM s lambda ≥ 0 := by
  unfold secularFunDeriv
  apply mul_nonneg
  · exact div_nonneg (le_of_lt (zero_lt_one)) (Nat.cast_nonneg _)
  · exact Finset.sum_nonneg (fun k _ => secularFunDeriv_term_nonneg es s lambda k)

/-- The derivative is strictly positive when λ is not a pole. -/
theorem secularFunDeriv_pos {n M : Nat} (es : EigenStructure n M)
    (hM : M > 0) (s : Real) (lambda : Real)
    (hne : ∀ k : Fin M, lambda ≠ s * es.eigenvalues k) :
    secularFunDeriv es hM s lambda > 0 := by
  unfold secularFunDeriv
  apply mul_pos
  · exact div_pos one_pos (Nat.cast_pos.mpr (Nat.pow_pos (by norm_num : 0 < 2)))
  · exact Finset.sum_pos (fun k _ => secularFunDeriv_term_pos es s lambda k (hne k))
      ⟨⟨0, hM⟩, Finset.mem_univ _⟩

/-! ## Properties at poles and boundaries -/

/-- The secular equation connects to the eigenvalue condition.
    From eigenvalue_condition_proof: λ is an eigenvalue of H(s) iff
    either λ = s·E_k (degenerate) or F(s,λ) = 0. -/
theorem secular_equation_characterizes_eigenvalues {n M : Nat} (es : EigenStructure n M)
    (hM : M > 0) (s : Real) (hs : 0 < s ∧ s < 1) (lambda : Real)
    (hne : ∀ k : Fin M, lambda ≠ s * es.eigenvalues k) :
    IsEigenvalue (adiabaticHam es s ⟨le_of_lt hs.1, le_of_lt hs.2⟩) lambda ↔
    secularFun es hM s lambda = 0 := by
  have hcond := eigenvalue_condition_proof es hM s hs lambda
  constructor
  · -- Forward: eigenvalue → F = 0
    intro heig
    rw [hcond] at heig
    rcases heig with ⟨z, hz_eq, _⟩ | ⟨hne', hsec⟩
    · -- Case λ = s·E_k: contradicts hne
      exact absurd hz_eq (hne (es.assignment z))
    · -- Case secular equation holds
      unfold secularFun
      linarith [hsec]
  · -- Backward: F = 0 → eigenvalue
    intro hF
    rw [hcond]
    right
    constructor
    · exact hne
    · -- secularFun = 0 means 1/(1-s) = (1/N) Σ d_k/(sE_k - λ)
      unfold secularFun at hF
      linarith

/-! ## Monotonicity of the secular function -/

/-- Each term d_k/(sE_k - λ) is strictly increasing in λ when the denominator
    doesn't change sign. The proof uses: if λ₁ < λ₂ and sE_k is on the same side
    of both, then d_k/(sE_k - λ₂) > d_k/(sE_k - λ₁). -/
lemma secularTerm_strictMono {n M : Nat} (es : EigenStructure n M)
    (s : Real) (lambda1 lambda2 : Real) (k : Fin M)
    (hlt : lambda1 < lambda2)
    (hne1 : lambda1 ≠ s * es.eigenvalues k)
    (hne2 : lambda2 ≠ s * es.eigenvalues k)
    -- Both λ's on the same side of sE_k (no sign change)
    (hsame : (s * es.eigenvalues k - lambda1) * (s * es.eigenvalues k - lambda2) > 0) :
    (es.degeneracies k : Real) / (s * es.eigenvalues k - lambda1) <
    (es.degeneracies k : Real) / (s * es.eigenvalues k - lambda2) := by
  -- Algebraic approach: show d/(a-λ₂) - d/(a-λ₁) > 0
  -- = d(λ₂-λ₁)/((a-λ₂)(a-λ₁)) > 0  since d > 0, λ₂-λ₁ > 0, product > 0
  set a := s * es.eigenvalues k
  set d := (es.degeneracies k : Real)
  have hd_pos : d > 0 := Nat.cast_pos.mpr (es.deg_positive k)
  have ha1 : a - lambda1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hne1)
  have ha2 : a - lambda2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hne2)
  suffices h : d / (a - lambda2) - d / (a - lambda1) > 0 by linarith
  rw [div_sub_div _ _ ha2 ha1]
  apply div_pos
  · -- Numerator: d*(a-λ₁) - (a-λ₂)*d = d*(λ₂-λ₁) > 0
    have hnum : d * (a - lambda1) - (a - lambda2) * d = d * (lambda2 - lambda1) := by ring
    rw [hnum]
    exact mul_pos hd_pos (sub_pos.mpr hlt)
  · -- Denominator: (a-λ₂)*(a-λ₁) > 0
    have hprod : (a - lambda2) * (a - lambda1) = (a - lambda1) * (a - lambda2) := mul_comm _ _
    rw [hprod]; exact hsame

/-- When two points are in the same interval between poles, the denominator products are positive. -/
private lemma same_interval_product_pos {a x y : Real}
    (h : (a < x ∧ a < y) ∨ (x < a ∧ y < a) ∨ (a ≤ x ∧ y ≤ a))
    (hlt : x < y) :
    (a - x) * (a - y) > 0 := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact mul_pos_of_neg_of_neg (sub_neg.mpr h1) (sub_neg.mpr h2)
  · exact mul_pos (sub_pos.mpr h1) (sub_pos.mpr h2)
  · linarith

/-- The secular function evaluated at two points in the same interval.
    If λ₁ < λ₂ and both are in the same interval between poles,
    then F(s,λ₁) < F(s,λ₂).

    This is because ∂F/∂λ > 0 on each pole-free interval. -/
theorem secularFun_strictMono_on_interval {n M : Nat} (es : EigenStructure n M)
    (hM : M > 0) (s : Real) (lambda1 lambda2 : Real)
    (hlt : lambda1 < lambda2)
    (hne1 : ∀ k : Fin M, lambda1 ≠ s * es.eigenvalues k)
    (hne2 : ∀ k : Fin M, lambda2 ≠ s * es.eigenvalues k)
    -- Both λ₁, λ₂ are in the same interval (no pole between them)
    (h_same_interval : ∀ k : Fin M,
      (s * es.eigenvalues k < lambda1 ∧ s * es.eigenvalues k < lambda2) ∨
      (lambda1 < s * es.eigenvalues k ∧ lambda2 < s * es.eigenvalues k) ∨
      (s * es.eigenvalues k ≤ lambda1 ∧ lambda2 ≤ s * es.eigenvalues k)) :
    secularFun es hM s lambda1 < secularFun es hM s lambda2 := by
  -- Each term d_k/(sE_k - λ) is strictly increasing in λ on each pole-free interval.
  -- Sum of strictly increasing functions is strictly increasing. The -1/(1-s) cancels.
  unfold secularFun
  -- Suffices to show the sum part is strictly increasing (constant cancels)
  suffices h_sum :
      (Finset.sum Finset.univ (fun k : Fin M =>
        (es.degeneracies k : Real) / (s * es.eigenvalues k - lambda1))) <
      (Finset.sum Finset.univ (fun k : Fin M =>
        (es.degeneracies k : Real) / (s * es.eigenvalues k - lambda2))) by
    have hN_pos : (1 : Real) / (qubitDim n : Real) > 0 :=
      div_pos one_pos (Nat.cast_pos.mpr (Nat.pow_pos (by norm_num : 0 < 2)))
    linarith [mul_lt_mul_of_pos_left h_sum hN_pos]
  apply Finset.sum_lt_sum
  · -- Each term: term(lambda1) ≤ term(lambda2)
    intro k _
    exact le_of_lt (secularTerm_strictMono es s lambda1 lambda2 k hlt (hne1 k) (hne2 k)
      (same_interval_product_pos (h_same_interval k) hlt))
  · -- At least one strict: use k = 0
    exact ⟨⟨0, hM⟩, Finset.mem_univ _, secularTerm_strictMono es s lambda1 lambda2 ⟨0, hM⟩ hlt
      (hne1 _) (hne2 _) (same_interval_product_pos (h_same_interval _) hlt)⟩

/-! ## Root structure -/

/-- The secular function goes to +∞ as λ approaches a pole from below. -/
theorem secularFun_tendsto_top_from_below {n M : Nat} (es : EigenStructure n M)
    (hM : M > 0) (s : Real) (hs : 0 < s) (k : Fin M) :
    ∀ ε > 0, ∃ δ > 0, ∀ lambda,
      s * es.eigenvalues k - δ < lambda →
      lambda < s * es.eigenvalues k →
      secularFun es hM s lambda > 1/ε := by
  sorry -- TODO: d_k/(sE_k - λ) → +∞ as λ → (sE_k)⁻

/-- The secular function goes to -∞ as λ approaches a pole from above. -/
theorem secularFun_tendsto_bot_from_above {n M : Nat} (es : EigenStructure n M)
    (hM : M > 0) (s : Real) (hs : 0 < s) (k : Fin M) :
    ∀ ε > 0, ∃ δ > 0, ∀ lambda,
      s * es.eigenvalues k < lambda →
      lambda < s * es.eigenvalues k + δ →
      secularFun es hM s lambda < -(1/ε) := by
  sorry -- TODO: d_k/(sE_k - λ) → -∞ as λ → (sE_k)⁺

/-- Below the lowest pole, F(s,λ) → -1/(1-s) < 0 as λ → -∞. -/
theorem secularFun_neg_at_neg_infty {n M : Nat} (es : EigenStructure n M)
    (hM : M > 0) (s : Real) (hs : 0 < s ∧ s < 1) :
    ∀ ε > 0, ∃ L, ∀ lambda,
      lambda < L →
      (∀ k : Fin M, lambda < s * es.eigenvalues k) →
      |secularFun es hM s lambda + 1/(1-s)| < ε := by
  intro ε hε
  -- Choose L so that sE₀ - λ > 1/ε
  use s * es.eigenvalues ⟨0, hM⟩ - 1/ε
  intro lambda hL h_below
  -- Abbreviations
  set N := (qubitDim n : Real) with hN_def
  set E₀ := es.eigenvalues ⟨0, hM⟩
  -- Positivity
  have hN_pos : N > 0 := Nat.cast_pos.mpr (Nat.pow_pos (by norm_num : 0 < 2))
  have hdiff_pos : ∀ k : Fin M, s * es.eigenvalues k - lambda > 0 :=
    fun k => sub_pos.mpr (h_below k)
  -- Key identity: secularFun + 1/(1-s) = (1/N) * Σ d_k/(sE_k - λ)
  -- Since value ≥ 0, suffices to show value < ε
  suffices h_bound : (1 / N) * Finset.sum Finset.univ (fun k : Fin M =>
      (es.degeneracies k : Real) / (s * es.eigenvalues k - lambda)) < ε by
    have hkey : secularFun es hM s lambda + 1 / (1 - s) =
        (1 / N) * Finset.sum Finset.univ (fun k : Fin M =>
          (es.degeneracies k : Real) / (s * es.eigenvalues k - lambda)) := by
      unfold secularFun; ring
    rw [hkey]
    have hnn : 0 ≤ (1 / N) * Finset.sum Finset.univ (fun k : Fin M =>
        (es.degeneracies k : Real) / (s * es.eigenvalues k - lambda)) :=
      mul_nonneg (div_nonneg one_pos.le hN_pos.le)
        (Finset.sum_nonneg fun k _ => le_of_lt (div_pos (Nat.cast_pos.mpr (es.deg_positive k)) (hdiff_pos k)))
    rw [abs_of_nonneg hnn]; exact h_bound
  -- E₀ ≤ E_k for all k (eigenvalues ordered)
  have hE₀_min : ∀ k : Fin M, E₀ ≤ es.eigenvalues k := by
    intro k
    by_cases hk0 : (k : Nat) = 0
    · have : k = ⟨0, hM⟩ := Fin.ext hk0
      rw [this]
    · exact le_of_lt (es.eigenval_ordered ⟨0, hM⟩ k (show (0 : Nat) < k from by omega))
  -- sE₀ - λ > 0
  have hbase_pos : s * E₀ - lambda > 0 := hdiff_pos ⟨0, hM⟩
  -- sE₀ - λ > 1/ε
  have hbase_large : s * E₀ - lambda > 1 / ε := by linarith
  -- Each term d_k/(sE_k - λ) ≤ d_k/(sE₀ - λ)  [bigger denom → smaller frac]
  have h_term_le : ∀ k ∈ Finset.univ, (es.degeneracies k : Real) / (s * es.eigenvalues k - lambda) ≤
      (es.degeneracies k : Real) / (s * E₀ - lambda) := by
    intro k _
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) hbase_pos
    linarith [mul_le_mul_of_nonneg_left (hE₀_min k) (le_of_lt hs.1)]
  -- Σ d_k/(sE_k - λ) ≤ Σ d_k/(sE₀ - λ) = (Σ d_k)/(sE₀ - λ) = N/(sE₀ - λ)
  have hsum_le : Finset.sum Finset.univ (fun k : Fin M =>
      (es.degeneracies k : Real) / (s * es.eigenvalues k - lambda)) ≤
      N / (s * E₀ - lambda) := by
    calc Finset.sum Finset.univ (fun k => (↑(es.degeneracies k) : Real) / (s * es.eigenvalues k - lambda))
        ≤ Finset.sum Finset.univ (fun k => (↑(es.degeneracies k) : Real) / (s * E₀ - lambda)) :=
          Finset.sum_le_sum h_term_le
      _ = (Finset.sum Finset.univ (fun k : Fin M => (es.degeneracies k : Real))) / (s * E₀ - lambda) :=
          (Finset.sum_div ..).symm
      _ = N / (s * E₀ - lambda) := by
          congr 1
          -- Σ (d_k : ℝ) = N = qubitDim n
          rw [hN_def]
          have h := es.deg_sum  -- : Σ d_k = qubitDim n (in ℕ)
          exact_mod_cast h
  -- (1/N) * sum ≤ (1/N) * N/(sE₀ - λ) = 1/(sE₀ - λ) < ε
  calc (1 / N) * Finset.sum Finset.univ _
      ≤ (1 / N) * (N / (s * E₀ - lambda)) :=
        mul_le_mul_of_nonneg_left hsum_le (div_nonneg one_pos.le hN_pos.le)
    _ = 1 / (s * E₀ - lambda) := by field_simp
    _ < ε := by
        have h := (one_div_lt_one_div hbase_pos (div_pos one_pos hε)).mpr hbase_large
        rwa [one_div_one_div] at h

/-- There is exactly one root of F(s,·) in (-∞, s·E₀).
    This root is the ground state eigenvalue of H(s). -/
theorem exists_unique_root_below_ground {n M : Nat} (es : EigenStructure n M)
    (hM : M > 0) (s : Real) (hs : 0 < s ∧ s < 1) :
    ∃! lambda, lambda < s * es.eigenvalues ⟨0, hM⟩ ∧
      secularFun es hM s lambda = 0 := by
  sorry -- TODO: IVT + monotonicity

/-- The ground state eigenvalue of H(s) is determined by the secular equation.
    It is the unique λ < s·E₀ with F(s,λ) = 0. -/
theorem ground_eigenvalue_is_secular_root {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (s : Real) (hs : 0 < s ∧ s < 1) :
    ∃ E0 : Real,
      IsEigenvalue (adiabaticHam es s ⟨le_of_lt hs.1, le_of_lt hs.2⟩) E0 ∧
      E0 < s * es.eigenvalues ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩ ∧
      secularFun es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM) s E0 = 0 ∧
      (∀ E, IsEigenvalue (adiabaticHam es s ⟨le_of_lt hs.1, le_of_lt hs.2⟩) E → E0 ≤ E) := by
  sorry -- TODO: Combine secular equation with spectral theory

/-! ## Behavior near the avoided crossing -/

/-- At s = s*, the two eigenvalues closest to the crossing point are separated by g_min.

    The secular equation near s* reduces to a 2×2 effective system:
    F(s,λ) ≈ 0 gives λ²(s) ≈ λ_cross² + c·(s-s*)²
    where λ_cross corresponds to the crossing eigenvalue and c depends on A₁, A₂. -/
theorem gap_near_avoided_crossing {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (hcond : spectralConditionForBounds es hM)
    (s : Real) (hs : 0 < s ∧ s < 1) :
    ∃ (E0 E1 : Real),
      IsEigenvalue (adiabaticHam es s ⟨le_of_lt hs.1, le_of_lt hs.2⟩) E0 ∧
      IsEigenvalue (adiabaticHam es s ⟨le_of_lt hs.1, le_of_lt hs.2⟩) E1 ∧
      E0 < E1 ∧
      (∀ E, IsEigenvalue (adiabaticHam es s ⟨le_of_lt hs.1, le_of_lt hs.2⟩) E → E0 ≤ E) ∧
      -- The gap is bounded below by g_min/4
      E1 - E0 ≥ minimumGap es hM / 4 := by
  sorry -- TODO: Main spectral analysis result

end UAQO.Proofs.Spectral.SecularEquation
