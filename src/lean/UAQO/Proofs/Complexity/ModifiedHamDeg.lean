/-
  Proofs for modified Hamiltonian degeneracy axioms in Hardness.lean.

  Status:
  - modifiedHam_deg_sum: FULLY PROVED in Hardness.lean (no longer an axiom)
  - modifiedHam_deg_count: Proved here using bijection argument

  The construction is now simpler: modifiedHamiltonian returns EigenStructure (n+1) M
  (same number of levels, but doubled degeneracies). The level M issue from the
  original formulation has been fixed by removing level M entirely.
-/
import UAQO.Complexity.Hardness
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace UAQO.Complexity.Proofs

open UAQO UAQO.Complexity

/-- For z in Fin(qubitDim(n+1)), z.val / 2 < qubitDim n always holds. -/
lemma div2_lt_qubitDim {n : Nat} (z : Fin (qubitDim (n + 1))) : z.val / 2 < qubitDim n := by
  have hz := z.isLt
  simp only [qubitDim_succ] at hz
  omega

/-- The modifiedHam_assignment function always returns a valid index in Fin M. -/
lemma modifiedHam_assignment_lt_M {n M : Nat} (es : EigenStructure n M) (hM : M > 0)
    (z : Fin (qubitDim (n + 1))) :
    (modifiedHam_assignment es hM z).val < M := by
  exact (modifiedHam_assignment es hM z).isLt

/-- Two z values map to the same eigenvalue index k iff they share the same n_part and
    the original assignment maps that n_part to k.

    Since modifiedHam_assignment es hM z = es.assignment ⟨z.val / 2, _⟩, two z values
    z1 and z2 map to the same k iff z1.val / 2 = z2.val / 2 and es.assignment maps that
    value to k. -/
lemma modifiedHam_assignment_eq_iff {n M : Nat} (es : EigenStructure n M) (hM : M > 0)
    (z : Fin (qubitDim (n + 1))) (k : Fin M) :
    modifiedHam_assignment es hM z = k ↔
    es.assignment ⟨z.val / 2, div2_lt_qubitDim z⟩ = k := by
  unfold modifiedHam_assignment
  rfl

/-- For each np : Fin (qubitDim n), both z = 2*np and z = 2*np+1 have z.val / 2 = np.val. -/
lemma div2_of_double {n : Nat} (np : Fin (qubitDim n)) :
    (2 * np.val) / 2 = np.val := Nat.mul_div_cancel_left np.val (by norm_num : 0 < 2)

lemma div2_of_double_plus_one {n : Nat} (np : Fin (qubitDim n)) :
    (2 * np.val + 1) / 2 = np.val := by
  have h1 : 2 * np.val / 2 = np.val := Nat.mul_div_cancel_left np.val (by norm_num : 0 < 2)
  have h2 : (2 * np.val + 1) / 2 = 2 * np.val / 2 := by omega
  omega

/-- 2 * np.val < qubitDim (n + 1) for np : Fin (qubitDim n). -/
lemma double_lt_qubitDim_succ {n : Nat} (np : Fin (qubitDim n)) :
    2 * np.val < qubitDim (n + 1) := by
  have h := np.isLt
  simp only [qubitDim_succ]
  omega

/-- 2 * np.val + 1 < qubitDim (n + 1) for np : Fin (qubitDim n). -/
lemma double_plus_one_lt_qubitDim_succ {n : Nat} (np : Fin (qubitDim n)) :
    2 * np.val + 1 < qubitDim (n + 1) := by
  have h := np.isLt
  simp only [qubitDim_succ]
  omega

/-- 2 * k % 2 = 0 for any k. -/
lemma double_mod_two (k : Nat) : 2 * k % 2 = 0 := Nat.mul_mod_right 2 k

/-- (2 * k + 1) % 2 = 1 for any k. -/
lemma double_plus_one_mod_two (k : Nat) : (2 * k + 1) % 2 = 1 := by omega

/-- The filter of z values mapping to k can be decomposed by parity. -/
lemma filter_by_parity {n M : Nat} (es : EigenStructure n M) (hM : M > 0) (k : Fin M) :
    (Finset.filter (fun z : Fin (qubitDim (n + 1)) =>
      modifiedHam_assignment es hM z = k) Finset.univ) =
    (Finset.filter (fun z : Fin (qubitDim (n + 1)) =>
      modifiedHam_assignment es hM z = k ∧ z.val % 2 = 0) Finset.univ) ∪
    (Finset.filter (fun z : Fin (qubitDim (n + 1)) =>
      modifiedHam_assignment es hM z = k ∧ z.val % 2 = 1) Finset.univ) := by
  ext z
  simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
  constructor
  · intro hz
    by_cases hparity : z.val % 2 = 0
    · left; exact ⟨hz, hparity⟩
    · right
      have : z.val % 2 < 2 := Nat.mod_lt z.val (by norm_num)
      have : z.val % 2 = 0 ∨ z.val % 2 = 1 := by omega
      cases this with
      | inl h => exact absurd h hparity
      | inr h => exact ⟨hz, h⟩
  · intro hz
    cases hz with
    | inl h => exact h.1
    | inr h => exact h.1

/-- The even and odd filters are disjoint. -/
lemma filter_parity_disjoint {n M : Nat} (es : EigenStructure n M) (hM : M > 0) (k : Fin M) :
    Disjoint
      (Finset.filter (fun z : Fin (qubitDim (n + 1)) =>
        modifiedHam_assignment es hM z = k ∧ z.val % 2 = 0) Finset.univ)
      (Finset.filter (fun z : Fin (qubitDim (n + 1)) =>
        modifiedHam_assignment es hM z = k ∧ z.val % 2 = 1) Finset.univ) := by
  rw [Finset.disjoint_filter]
  intro z _ h0 h1
  -- h0 : z.val % 2 = 0, h1 : z.val % 2 = 1
  omega

/-- The even z-values form a bijection with the source filter. -/
lemma even_filter_card {n M : Nat} (es : EigenStructure n M) (hM : M > 0) (k : Fin M) :
    (Finset.filter (fun z : Fin (qubitDim (n + 1)) =>
      modifiedHam_assignment es hM z = k ∧ z.val % 2 = 0) Finset.univ).card =
    (Finset.filter (fun np : Fin (qubitDim n) => es.assignment np = k) Finset.univ).card := by
  apply Finset.card_bij (fun z _ => ⟨z.val / 2, div2_lt_qubitDim z⟩)
  · -- hi: maps into target
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    rw [modifiedHam_assignment_eq_iff] at hz
    exact hz.1
  · -- i_inj: injectivity
    intro z1 hz1 z2 hz2 heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz1 hz2
    simp only [Fin.ext_iff] at heq ⊢
    have hz1_even : z1.val = 2 * (z1.val / 2) := by
      have := Nat.div_add_mod z1.val 2; omega
    have hz2_even : z2.val = 2 * (z2.val / 2) := by
      have := Nat.div_add_mod z2.val 2; omega
    omega
  · -- i_surj: surjectivity
    intro np hnp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hnp ⊢
    let z : Fin (qubitDim (n + 1)) := ⟨2 * np.val, double_lt_qubitDim_succ np⟩
    refine ⟨z, ?_, ?_⟩
    · constructor
      · rw [modifiedHam_assignment_eq_iff]
        show es.assignment ⟨z.val / 2, _⟩ = k
        have h : z.val / 2 = np.val := div2_of_double np
        have heq : (⟨z.val / 2, div2_lt_qubitDim z⟩ : Fin (qubitDim n)) = np := by
          simp only [h]
        rw [heq]; exact hnp
      · exact double_mod_two np.val
    · simp only [Fin.ext_iff]
      exact div2_of_double np

/-- The odd z-values form a bijection with the source filter. -/
lemma odd_filter_card {n M : Nat} (es : EigenStructure n M) (hM : M > 0) (k : Fin M) :
    (Finset.filter (fun z : Fin (qubitDim (n + 1)) =>
      modifiedHam_assignment es hM z = k ∧ z.val % 2 = 1) Finset.univ).card =
    (Finset.filter (fun np : Fin (qubitDim n) => es.assignment np = k) Finset.univ).card := by
  apply Finset.card_bij (fun z _ => ⟨z.val / 2, div2_lt_qubitDim z⟩)
  · -- hi: maps into target
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    rw [modifiedHam_assignment_eq_iff] at hz
    exact hz.1
  · -- i_inj: injectivity
    intro z1 hz1 z2 hz2 heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz1 hz2
    simp only [Fin.ext_iff] at heq ⊢
    have hz1_odd : z1.val = 2 * (z1.val / 2) + 1 := by
      have := Nat.div_add_mod z1.val 2; omega
    have hz2_odd : z2.val = 2 * (z2.val / 2) + 1 := by
      have := Nat.div_add_mod z2.val 2; omega
    omega
  · -- i_surj: surjectivity
    intro np hnp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hnp ⊢
    let z : Fin (qubitDim (n + 1)) := ⟨2 * np.val + 1, double_plus_one_lt_qubitDim_succ np⟩
    refine ⟨z, ?_, ?_⟩
    · constructor
      · rw [modifiedHam_assignment_eq_iff]
        show es.assignment ⟨z.val / 2, _⟩ = k
        have h : z.val / 2 = np.val := div2_of_double_plus_one np
        have heq : (⟨z.val / 2, div2_lt_qubitDim z⟩ : Fin (qubitDim n)) = np := by
          simp only [h]
        rw [heq]; exact hnp
      · exact double_plus_one_mod_two np.val
    · simp only [Fin.ext_iff]
      exact div2_of_double_plus_one np

/-- The degeneracy count in the modified Hamiltonian: each level has twice the original count.

    This is the key theorem that completes the modifiedHam_deg_count proof.
    For each np with es.assignment np = k, both z = 2*np and z = 2*np+1 map to k.
    So the new degeneracy is exactly 2 times the original. -/
theorem modifiedHam_deg_count_proof {n M : Nat} (es : EigenStructure n M) (hM : M > 0) :
    ∀ k : Fin M,
      es.degeneracies k * 2 =
      (Finset.filter (fun z : Fin (qubitDim (n + 1)) =>
        modifiedHam_assignment es hM z = k) Finset.univ).card := by
  intro k
  rw [filter_by_parity es hM k]
  rw [Finset.card_union_of_disjoint (filter_parity_disjoint es hM k)]
  rw [even_filter_card es hM k, odd_filter_card es hM k]
  have hsource : (Finset.filter (fun np : Fin (qubitDim n) => es.assignment np = k) Finset.univ).card
      = es.degeneracies k := (es.deg_count k).symm
  rw [hsource]
  ring

end UAQO.Complexity.Proofs
