/-
  Proofs for beta-modified Hamiltonian axioms in Hardness.lean.

  Status:
  - betaModifiedHam_deg_sum: FULLY PROVED
  - betaModifiedHam_deg_count: Not proved (needs assignment function analysis)
  - betaModifiedHam_eigenval_ordered: Case 1 proved, Case 2 needs universal gap constraint
  - betaModifiedHam_eigenval_ordered_strict: Case 1 proved, Case 2 needs universal gap constraint
  - betaModifiedHam_eigenval_bounds: Lower bound proved, upper bound needs constraint
-/
import UAQO.Complexity.Hardness
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

namespace UAQO.Complexity.Proofs

open UAQO UAQO.Complexity

/-- For k in Fin (2*M), k.val / 2 < M always holds. -/
lemma div2_lt_of_fin_2M {M : Nat} (k : Fin (2 * M)) : k.val / 2 < M := by
  have hk := k.isLt
  exact Nat.div_lt_of_lt_mul hk

/-- Helper: if i/2 = j/2 and i < j (as Nat), then i is even and j = i + 1. -/
lemma same_div2_implies_consec {i j : Nat} (h_div : i / 2 = j / 2) (h_lt : i < j) :
    i % 2 = 0 ∧ j = i + 1 := by
  have hi_mod := Nat.div_add_mod i 2
  have hj_mod := Nat.div_add_mod j 2
  have hi_rem : i % 2 < 2 := Nat.mod_lt i (by norm_num)
  have hj_rem : j % 2 < 2 := Nat.mod_lt j (by norm_num)
  constructor
  · by_contra h
    have : i % 2 = 1 := by omega
    omega
  · omega

/-- The even indices in Fin (2*M) are in bijection with Fin M via k ↦ 2k. -/
def evenBij (M : Nat) (hM : M > 0) : Fin M → Fin (2 * M) :=
  fun i => ⟨2 * i.val, by omega⟩

/-- The odd indices in Fin (2*M) are in bijection with Fin M via k ↦ 2k+1. -/
def oddBij (M : Nat) (hM : M > 0) : Fin M → Fin (2 * M) :=
  fun i => ⟨2 * i.val + 1, by omega⟩

/-- The degeneracy sum in the beta-modified Hamiltonian equals the new Hilbert space dimension.

    Each k in Fin (2*M) has origIdx = k.val / 2 < M, so the "else 1" branch is never taken.
    Sum = Σ_{k=0}^{2M-1} d_{k/2} = Σ_{i=0}^{M-1} (d_i + d_i) = 2 * Σ d_i = 2 * N = qubitDim (n+1). -/
theorem betaModifiedHam_deg_sum_proof {n M : Nat} (es : EigenStructure n M) (hM : M > 0) :
    Finset.sum Finset.univ (fun k : Fin (2 * M) =>
      let origIdx := k.val / 2
      if hOrig : origIdx < M then es.degeneracies ⟨origIdx, hOrig⟩ else 1) = qubitDim (n + 1) := by
  -- Step 1: Simplify away the dite (the else branch is never taken)
  have hSimp : ∀ k : Fin (2 * M), (let origIdx := k.val / 2
       if hOrig : origIdx < M then es.degeneracies ⟨origIdx, hOrig⟩ else 1) =
       es.degeneracies ⟨k.val / 2, div2_lt_of_fin_2M k⟩ := by
    intro k
    simp only [div2_lt_of_fin_2M k, dite_true]
  conv_lhs => arg 2; ext k; rw [hSimp k]

  -- Step 2: Show sum = 2 * (sum of original degeneracies)
  rw [qubitDim_succ]

  -- Step 3: Reindex the sum
  -- Sum over Fin (2*M) where f(k) = d_{k/2}
  -- = Sum over even k of d_{k/2} + Sum over odd k of d_{k/2}
  -- = Sum over Fin M of d_i + Sum over Fin M of d_i
  -- = 2 * Sum over Fin M of d_i

  -- Use Fintype.sum_equiv to reindex
  have h2M_pos : 0 < 2 * M := Nat.mul_pos (by norm_num) hM

  -- Show that the sum equals 2 * (sum of degeneracies)
  -- Each degeneracy d_i appears twice: once for k = 2i (even), once for k = 2i+1 (odd)
  have hSum : Finset.sum Finset.univ (fun k : Fin (2 * M) =>
        es.degeneracies ⟨k.val / 2, div2_lt_of_fin_2M k⟩) =
      2 * Finset.sum Finset.univ es.degeneracies := by
    -- Split Fin (2*M) into evens and odds
    have hSplit : (Finset.univ : Finset (Fin (2 * M))) =
        Finset.filter (fun k => k.val % 2 = 0) Finset.univ ∪
        Finset.filter (fun k => k.val % 2 = 1) Finset.univ := by
      ext k
      simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and]
      have := Nat.mod_two_eq_zero_or_one k.val
      tauto
    have hDisj : Disjoint
        (Finset.filter (fun k : Fin (2 * M) => k.val % 2 = 0) Finset.univ)
        (Finset.filter (fun k : Fin (2 * M) => k.val % 2 = 1) Finset.univ) := by
      rw [Finset.disjoint_filter]
      intro k _ hk0
      omega
    rw [hSplit, Finset.sum_union hDisj, Finset.mul_sum]
    -- Sum over evens: each even k = 2i maps to i with d_{k/2} = d_i
    -- Sum over odds: each odd k = 2i+1 maps to i with d_{k/2} = d_i
    -- Both sums equal Σ d_i, so total = 2 * Σ d_i
    have hEvenSum : Finset.sum (Finset.filter (fun k : Fin (2 * M) => k.val % 2 = 0) Finset.univ)
        (fun k => es.degeneracies ⟨k.val / 2, div2_lt_of_fin_2M k⟩) =
        Finset.sum Finset.univ es.degeneracies := by
      symm
      apply Finset.sum_nbij (fun i : Fin M => (⟨2 * i.val, by omega⟩ : Fin (2 * M)))
      · intro i _
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact Nat.mul_mod_right 2 i.val
      · intro i j _ _ h
        simp only [Fin.mk.injEq] at h
        ext; omega
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        refine ⟨⟨k.val / 2, div2_lt_of_fin_2M k⟩, Finset.mem_univ _, ?_⟩
        simp only [Fin.mk.injEq]
        have : k.val = 2 * (k.val / 2) + k.val % 2 := (Nat.div_add_mod k.val 2).symm
        omega
      · intro i _
        congr 1
        simp only [Fin.ext_iff, Fin.val_mk]
        exact Nat.mul_div_cancel_left i.val (by norm_num : 0 < 2)
    have hOddSum : Finset.sum (Finset.filter (fun k : Fin (2 * M) => k.val % 2 = 1) Finset.univ)
        (fun k => es.degeneracies ⟨k.val / 2, div2_lt_of_fin_2M k⟩) =
        Finset.sum Finset.univ es.degeneracies := by
      symm
      apply Finset.sum_nbij (fun i : Fin M => (⟨2 * i.val + 1, by omega⟩ : Fin (2 * M)))
      · intro i _
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      · intro i j _ _ h
        have h' := Fin.val_eq_val.mpr h
        simp only [Fin.val_mk] at h'
        ext; omega
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        refine ⟨⟨k.val / 2, div2_lt_of_fin_2M k⟩, Finset.mem_univ _, ?_⟩
        ext
        simp only [Fin.val_mk]
        have : k.val = 2 * (k.val / 2) + k.val % 2 := (Nat.div_add_mod k.val 2).symm
        omega
      · intro i _
        congr 1
        ext
        simp [Nat.add_div_right _ (by norm_num : 0 < 2), Nat.mul_div_cancel_left i.val (by norm_num : 0 < 2)]
    rw [hEvenSum, hOddSum, ← two_mul]
  rw [hSum, es.deg_sum]

/-- The degeneracy count matches the assignment function. -/
theorem betaModifiedHam_deg_count_proof {n M : Nat} (es : EigenStructure n M) (hM : M > 0) :
    ∀ k : Fin (2 * M),
      (let origIdx := k.val / 2
       if hOrig : origIdx < M then es.degeneracies ⟨origIdx, hOrig⟩ else 1) =
      (Finset.filter (fun z : Fin (qubitDim (n + 1)) =>
        betaModifiedHam_assignment es hM z = k) Finset.univ).card := by
  intro k
  have horigK : k.val / 2 < M := div2_lt_of_fin_2M k
  simp only [horigK, dite_true]
  -- Need to count z such that betaModifiedHam_assignment es hM z = k
  -- betaModifiedHam_assignment: z ↦ 2 * (es.assignment (z/2)) + (z % 2)
  -- So we need: 2 * orig_idx + spin = k.val
  -- This means: orig_idx = k.val / 2 and spin = k.val % 2
  -- Count of such z = count of z where es.assignment(z/2) = k/2 and z % 2 = k % 2
  -- = count of orig states with assignment k/2 (since each has exactly one spin value matching)
  -- = es.degeneracies(k/2)
  sorry

/-- Eigenvalue ordering in beta-modified Hamiltonian (weak inequality). -/
theorem betaModifiedHam_eigenval_ordered_proof {n M : Nat} (es : EigenStructure n M) (hM : M > 0)
    (beta : Real) (hbeta : 0 < beta ∧ beta < 1) :
    ∀ i j : Fin (2 * M), i < j ->
      (let origI := i.val / 2
       let isUpperI := i.val % 2 = 1
       if hI : origI < M then es.eigenvalues ⟨origI, hI⟩ + if isUpperI then beta/2 else 0 else 1) <=
      (let origJ := j.val / 2
       let isUpperJ := j.val % 2 = 1
       if hJ : origJ < M then es.eigenvalues ⟨origJ, hJ⟩ + if isUpperJ then beta/2 else 0 else 1) := by
  intro i j hij
  have horigI : i.val / 2 < M := div2_lt_of_fin_2M i
  have horigJ : j.val / 2 < M := div2_lt_of_fin_2M j
  simp only [horigI, horigJ, dite_true]
  by_cases hEqOrig : i.val / 2 = j.val / 2
  · -- Same original level
    obtain ⟨hi_even, _⟩ := same_div2_implies_consec hEqOrig hij
    have hj_odd : j.val % 2 = 1 := by omega
    have hi_not_odd : ¬(i.val % 2 = 1) := by omega
    have hSameOrig : es.eigenvalues ⟨i.val / 2, horigI⟩ = es.eigenvalues ⟨j.val / 2, horigJ⟩ := by
      congr 1; exact Fin.ext hEqOrig
    simp only [hi_not_odd, hj_odd, ite_false, ite_true, add_zero]
    rw [hSameOrig]
    linarith [hbeta.1]
  · -- Different original levels
    have hOrigLt : i.val / 2 < j.val / 2 := by
      have h1 : i.val / 2 ≤ j.val / 2 := Nat.div_le_div_right (le_of_lt hij)
      omega
    have hElt : es.eigenvalues ⟨i.val / 2, horigI⟩ < es.eigenvalues ⟨j.val / 2, horigJ⟩ :=
      es.eigenval_ordered ⟨i.val / 2, horigI⟩ ⟨j.val / 2, horigJ⟩ hOrigLt
    -- For weak inequality with different original levels:
    -- Need E_origI + (0 or beta/2) <= E_origJ + (0 or beta/2)
    -- Worst case: E_origI + beta/2 <= E_origJ + 0
    -- This requires E_origJ - E_origI >= beta/2
    -- Without universal gap constraint, we cannot prove this
    sorry

/-- Strict eigenvalue ordering with gap constraint. -/
theorem betaModifiedHam_eigenval_ordered_strict_proof {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2)
    (beta : Real) (hbeta : 0 < beta ∧ beta < 1)
    (hgap : beta / 2 < spectralGapDiag es hM) :
    ∀ i j : Fin (2 * M), i < j ->
      (let origI := i.val / 2
       let isUpperI := i.val % 2 = 1
       if hI : origI < M then es.eigenvalues ⟨origI, hI⟩ + if isUpperI then beta/2 else 0 else 1) <
      (let origJ := j.val / 2
       let isUpperJ := j.val % 2 = 1
       if hJ : origJ < M then es.eigenvalues ⟨origJ, hJ⟩ + if isUpperJ then beta/2 else 0 else 1) := by
  intro i j hij
  have horigI : i.val / 2 < M := div2_lt_of_fin_2M i
  have horigJ : j.val / 2 < M := div2_lt_of_fin_2M j
  simp only [horigI, horigJ, dite_true]
  by_cases hEqOrig : i.val / 2 = j.val / 2
  · -- Same original level: i even, j odd, so E_i < E_i + beta/2
    obtain ⟨hi_even, _⟩ := same_div2_implies_consec hEqOrig hij
    have hj_odd : j.val % 2 = 1 := by omega
    have hi_not_odd : ¬(i.val % 2 = 1) := by omega
    have hSameOrig : es.eigenvalues ⟨i.val / 2, horigI⟩ = es.eigenvalues ⟨j.val / 2, horigJ⟩ := by
      congr 1; exact Fin.ext hEqOrig
    simp only [hi_not_odd, hj_odd, ite_false, ite_true, add_zero]
    rw [hSameOrig]
    linarith [hbeta.1]
  · -- Different original levels: need gap constraint
    have hOrigLt : i.val / 2 < j.val / 2 := by
      have h1 : i.val / 2 ≤ j.val / 2 := Nat.div_le_div_right (le_of_lt hij)
      omega
    have hElt : es.eigenvalues ⟨i.val / 2, horigI⟩ < es.eigenvalues ⟨j.val / 2, horigJ⟩ :=
      es.eigenval_ordered ⟨i.val / 2, horigI⟩ ⟨j.val / 2, horigJ⟩ hOrigLt
    -- The gap constraint hgap only constrains E_1 - E_0, not all consecutive gaps
    -- Need: E_origI + beta/2 < E_origJ
    -- Requires: E_origJ - E_origI > beta/2 for all origI < origJ
    -- This is NOT implied by spectralGapDiag = E_1 - E_0 alone
    sorry

/-- Eigenvalue bounds in beta-modified Hamiltonian. -/
theorem betaModifiedHam_eigenval_bounds_proof {n M : Nat} (es : EigenStructure n M)
    (beta : Real) (hbeta : 0 < beta ∧ beta < 1) (hM : M > 0) :
    ∀ k : Fin (2 * M),
      let origIdx := k.val / 2
      let isUpperLevel := k.val % 2 = 1
      0 <= (if hOrig : origIdx < M then
              es.eigenvalues ⟨origIdx, hOrig⟩ + if isUpperLevel then beta / 2 else 0
            else 1) ∧
      (if hOrig : origIdx < M then
         es.eigenvalues ⟨origIdx, hOrig⟩ + if isUpperLevel then beta / 2 else 0
       else 1) <= 1 := by
  intro k
  have horigK : k.val / 2 < M := div2_lt_of_fin_2M k
  simp only [horigK, dite_true]
  constructor
  · -- Lower bound: E_origK + (0 or beta/2) >= 0
    have hE_nonneg := (es.eigenval_bounds ⟨k.val / 2, horigK⟩).1
    split_ifs <;> linarith [hbeta.1]
  · -- Upper bound: E_origK + (0 or beta/2) <= 1
    have hE_le_one := (es.eigenval_bounds ⟨k.val / 2, horigK⟩).2
    split_ifs with h
    · -- Upper level: need E_origK + beta/2 <= 1, requires E_origK <= 1 - beta/2
      sorry
    · -- Lower level: E_origK + 0 <= 1
      linarith

end UAQO.Complexity.Proofs
