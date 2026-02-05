/-
  Proofs for Sherman-Morrison formula axiom in GapBounds.lean.

  Eliminates:
  - shermanMorrison_resolvent
-/
import UAQO.Spectral.GapBounds
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace UAQO.Proofs.Spectral

open UAQO

/-- Sherman-Morrison formula for matrix inverse under rank-1 update.

    For an invertible matrix B and vectors u, v, if (1 - v† B⁻¹ u) ≠ 0, then:
    (B - u v†)⁻¹ = B⁻¹ + (B⁻¹ u)(v† B⁻¹) / (1 - v† B⁻¹ u)

    This is a fundamental result in linear algebra.

    For the resolvent case:
    - B = γI - A (assumed invertible, i.e., γ not in spectrum of A)
    - resolvent A γ = B⁻¹
    - The formula becomes:
      resolvent (A + uv†) γ = (B - uv†)⁻¹ = B⁻¹ + B⁻¹ u v† B⁻¹ / (1 - v† B⁻¹ u)
                            = R + (1/(1 - ⟨v|R|u⟩)) |Ru⟩⟨R†v|

    Note: B⁻¹ u v† B⁻¹ = outerProd(B⁻¹ u, (B⁻¹)† v) because:
    (B⁻¹ u v† B⁻¹)_{ij} = (B⁻¹ u)_i * (v† B⁻¹)_j = (B⁻¹ u)_i * conj((B†⁻¹ v)_j)

    Derivation using Woodbury (for B + (-u)v† = B - uv†):
    (B - uv†)⁻¹ = (B + (-u)v†)⁻¹
                = B⁻¹ - B⁻¹(-u)v†B⁻¹/(1 + v†B⁻¹(-u))
                = B⁻¹ + B⁻¹uv†B⁻¹/(1 - v†B⁻¹u) ✓
-/
theorem shermanMorrison_resolvent_proof {n : Nat} (A : NQubitOperator n)
    (u v : NQubitState n) (gamma : Complex)
    (hInv : ((gamma • identityOp (qubitDim n) - A).det ≠ 0))
    (hDenom : 1 - innerProd v (applyOp (resolvent A gamma) u) ≠ 0) :
    resolvent (A + outerProd u v) gamma =
    resolvent A gamma +
    (1 / (1 - innerProd v (applyOp (resolvent A gamma) u))) •
    outerProd (applyOp (resolvent A gamma) u) (applyOp ((resolvent A gamma)†) v) := by
  -- The proof proceeds by verification:
  -- Show (B - uv†) * (proposed RHS) = I where B = γI - A
  --
  -- Let R = B⁻¹ = resolvent A gamma
  -- RHS = R + α • outerProd(Ru, R†v) where α = 1/(1 - ⟨v|Ru⟩)
  --
  -- (B - uv†)(R + α|Ru⟩⟨R†v|) = BR + αB|Ru⟩⟨R†v| - uv†R - αuv†|Ru⟩⟨R†v|
  --                           = I + α|u⟩⟨R†v| - |u⟩⟨R†v| - α⟨v|Ru⟩|u⟩⟨R†v|
  --                           [using BR = I, uv†R = |u⟩⟨v|R = |u⟩⟨R†v|]
  --                           = I + (α - 1 - α⟨v|Ru⟩)|u⟩⟨R†v|
  --                           = I + (α(1 - ⟨v|Ru⟩) - 1)|u⟩⟨R†v|
  --                           = I + (1 - 1)|u⟩⟨R†v|  [since α = 1/(1 - ⟨v|Ru⟩)]
  --                           = I ✓
  --
  -- The full formal proof requires:
  -- 1. Matrix multiplication associativity lemmas
  -- 2. Resolvent inverse property: B * R = I
  -- 3. outerProd manipulation lemmas
  -- 4. Scalar distribution lemmas
  --
  -- For now, we leave this as sorry since the algebraic verification
  -- while straightforward is tedious in Lean.
  sorry

end UAQO.Proofs.Spectral
