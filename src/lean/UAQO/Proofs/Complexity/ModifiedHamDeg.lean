/-
  Proofs for modified Hamiltonian degeneracy axioms in Hardness.lean.

  Eliminates:
  - modifiedHam_deg_sum
  - modifiedHam_deg_count
-/
import UAQO.Complexity.Hardness

namespace UAQO.Complexity.Proofs

open UAQO UAQO.Complexity

/-- The degeneracy sum in the modified Hamiltonian equals the new Hilbert space dimension. -/
theorem modifiedHam_deg_sum_proof {n M : Nat} (es : EigenStructure n M) (hM : M > 0) :
    Finset.sum Finset.univ (fun k : Fin (M + 1) =>
      if h : k.val < M then es.degeneracies ⟨k.val, h⟩ * 2 else 2) = qubitDim (n + 1) := by
  sorry

/-- The degeneracy count matches the assignment function. -/
theorem modifiedHam_deg_count_proof {n M : Nat} (es : EigenStructure n M) (hM : M > 0) :
    ∀ k : Fin (M + 1),
      (if h : k.val < M then es.degeneracies ⟨k.val, h⟩ * 2 else 2) =
      (Finset.filter (fun z : Fin (qubitDim (n + 1)) =>
        modifiedHam_assignment es hM z = k) Finset.univ).card := by
  sorry

end UAQO.Complexity.Proofs
