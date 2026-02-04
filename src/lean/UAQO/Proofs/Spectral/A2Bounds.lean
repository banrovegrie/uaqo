/-
  Analysis for A2 bounds in SpectralParameters.lean.

  Status:
  - Original `A2_lower_bound` axiom was INCORRECT (claimed lower bound, was actually upper bound)
  - Fixed: Now `A2_upper_bound` theorem in SpectralParameters.lean with correct direction
  - `A2_lower_bound_simple` theorem already provides a correct lower bound

  Analysis:
  - A2 = (1/N) * Sum_{k>=1} d_k / (E_k - E_0)^2
  - Delta = E_1 - E_0 (spectral gap)
  - For k >= 1: E_k >= E_1 (eigenvalues ordered), so E_k - E_0 >= Delta
  - Thus (E_k - E_0)^2 >= Delta^2, giving d_k/(E_k - E_0)^2 <= d_k/Delta^2

  Upper bound (now proved as theorem):
    A2 <= (1/N) * Sum_{k>=1} d_k / Delta^2 = (N - d0)/(N * Delta^2) = (1 - d0/N)/Delta^2

  Lower bound (existing theorem `A2_lower_bound_simple`):
    A2 >= d1/(N * Delta^2) (just the k=1 term)
-/
import UAQO.Spectral.SpectralParameters

namespace UAQO.Proofs.Spectral

open UAQO

/-- The upper bound A₂ ≤ (1 - d₀/N) / Δ² is now a theorem in SpectralParameters.lean.

    Key insight: Each term d_k/(E_k - E_0)^2 <= d_k/Delta^2 for k >= 1 because
    (E_k - E_0)^2 >= Delta^2. Summing gives the upper bound.

    The full proof requires careful Finset sum manipulations. -/
theorem A2_upper_bound_proof {n M : Nat} (es : EigenStructure n M) (hM : M >= 2) :
    A2 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM) <=
    (1 - (es.degeneracies ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩ : Real) / qubitDim n) /
    (spectralGapDiag es hM)^2 := by
  exact A2_upper_bound es hM

end UAQO.Proofs.Spectral
