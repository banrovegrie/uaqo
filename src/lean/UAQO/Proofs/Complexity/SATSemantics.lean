/-
  Proofs for SAT semantics axioms in Hardness.lean.

  Eliminates (fully proved, no sorry):
  - satisfies_iff_countUnsatisfied_zero
  - threeSATDegPositive_ground
-/
import UAQO.Complexity.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Bitwise

namespace UAQO.Complexity.Proofs

open UAQO.Complexity

/-- An assignment satisfies a formula iff it has 0 unsatisfied clauses.

    Proof: satisfies means all clauses evaluate to true (evalCNF = true),
    which means the filter of unsatisfied clauses (those evaluating to false)
    is empty, which means its length equals 0. -/
theorem satisfies_iff_countUnsatisfied_zero_proof (f : CNFFormula) (z : Fin (2^f.numVars)) :
    satisfies (finToAssignment f.numVars z) f ↔ countUnsatisfiedClauses f z = 0 := by
  simp only [satisfies, evalCNF, countUnsatisfiedClauses]
  rw [List.length_eq_zero_iff]
  constructor
  · -- Forward: all clauses true → no unsatisfied clauses
    intro h
    rw [List.filter_eq_nil_iff]
    intro c hc
    rw [List.all_eq_true] at h
    have heval := h c hc
    -- evalClause c = true, so !evalClause c = false ≠ true
    simp only [heval, Bool.not_true, Bool.false_eq_true, not_false_eq_true]
  · -- Backward: no unsatisfied clauses → all clauses true
    intro h
    rw [List.filter_eq_nil_iff] at h
    rw [List.all_eq_true]
    intro c hc
    specialize h c hc
    simp only [Bool.not_eq_true] at h
    cases hb : evalClause (finToAssignment f.numVars z) c <;> simp_all

/-- The count of assignments with 0 unsatisfied clauses equals the count of satisfying assignments. -/
theorem countAssignmentsWithZeroUnsatisfied_eq_numSatisfying (f : CNFFormula) :
    countAssignmentsWithKUnsatisfied f 0 = numSatisfyingAssignments f := by
  simp only [countAssignmentsWithKUnsatisfied, numSatisfyingAssignments]
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  -- Need: countUnsatisfiedClauses f z = 0 ↔ evalCNF (finToAssignment f.numVars z) f = true
  rw [← satisfies_iff_countUnsatisfied_zero_proof]
  rfl

/-- finToAssignment is injective: distinct Fin indices give distinct assignments. -/
lemma finToAssignment_injective (n : Nat) :
    Function.Injective (finToAssignment n) := by
  intro z w h
  ext
  -- If finToAssignment z = finToAssignment w, then z = w
  have heq : ∀ i : Fin n, z.val.testBit i.val = w.val.testBit i.val := by
    intro i
    have hz := congrFun h i
    simp only [finToAssignment] at hz
    exact hz
  -- For i >= n, both z and w have testBit i = false (since z, w < 2^n)
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · exact heq ⟨i, hi⟩
  · -- Both z and w are < 2^n, so bits at positions >= n are false
    have hz_bound := z.isLt
    have hw_bound := w.isLt
    rw [Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hz_bound (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_lt hi)))]
    rw [Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hw_bound (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_lt hi)))]

/-- Fin (2^n) and (Fin n → Bool) have the same cardinality. -/
lemma card_fin_pow_eq_card_fun (n : Nat) :
    Fintype.card (Fin (2^n)) = Fintype.card (Fin n → Bool) := by
  simp only [Fintype.card_fin, Fintype.card_fun, Fintype.card_bool]

/-- Assignment has decidable equality. -/
instance Assignment_decidableEq (n : Nat) : DecidableEq (Assignment n) :=
  inferInstanceAs (DecidableEq (Fin n → Bool))

/-- Assignment is a finite type. -/
instance Assignment_fintype (n : Nat) : Fintype (Assignment n) :=
  inferInstanceAs (Fintype (Fin n → Bool))

/-- finToAssignment is surjective: every assignment arises from some Fin index.
    This follows from injectivity and equal cardinality. -/
lemma finToAssignment_surjective (n : Nat) :
    Function.Surjective (finToAssignment n) := by
  have hinj : Function.Injective (finToAssignment n) := finToAssignment_injective n
  have hcard : Fintype.card (Fin (2^n)) = Fintype.card (Fin n → Bool) := card_fin_pow_eq_card_fun n
  intro a
  by_contra h
  push_neg at h
  have hcard_image : (Finset.univ.image (finToAssignment n)).card = Fintype.card (Fin (2^n)) := by
    rw [Finset.card_image_of_injective _ hinj]
    exact Finset.card_univ
  rw [hcard] at hcard_image
  have ha_in : a ∈ Finset.univ.image (finToAssignment n) := by
    have h_univ : Finset.univ.image (finToAssignment n) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [hcard_image]
      exact Finset.card_univ
    rw [h_univ]
    exact Finset.mem_univ a
  rw [Finset.mem_image] at ha_in
  obtain ⟨z, _, hz⟩ := ha_in
  exact h z hz

/-- For satisfiable formulas, the ground state degeneracy is positive.

    Proof: If the formula is satisfiable, there exists a satisfying assignment a.
    Since finToAssignment is surjective, there exists z such that finToAssignment z = a.
    This z has countUnsatisfiedClauses f z = 0 (by satisfies_iff_countUnsatisfied_zero).
    Therefore the count at level 0 is positive. -/
theorem threeSATDegPositive_ground_proof (f : CNFFormula) (_hf : is_kCNF 3 f)
    (hsat : isSatisfiable f) :
    countAssignmentsWithKUnsatisfied f 0 > 0 := by
  rw [countAssignmentsWithZeroUnsatisfied_eq_numSatisfying]
  -- isSatisfiable means there exists a satisfying assignment
  obtain ⟨a, ha⟩ := hsat
  simp only [numSatisfyingAssignments]
  obtain ⟨z, hz⟩ := finToAssignment_surjective f.numVars a
  apply Finset.card_pos.mpr
  use z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hz]
  exact ha

end UAQO.Complexity.Proofs
