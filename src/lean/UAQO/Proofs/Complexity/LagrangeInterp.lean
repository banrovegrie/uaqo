/-
  Proofs for Lagrange interpolation axiom in SharpP.lean.

  Eliminates:
  - lagrange_interpolation

  Uses Mathlib.LinearAlgebra.Lagrange for the standard Lagrange interpolation result.
-/
import UAQO.Complexity.SharpP
import Mathlib.LinearAlgebra.Lagrange

namespace UAQO.Complexity.Proofs

open UAQO.Complexity Polynomial

/-- Lagrange interpolation: M distinct points determine a unique polynomial of degree < M.

    Given M distinct points (x_0, y_0), ..., (x_{M-1}, y_{M-1}), there exists a unique
    polynomial p of degree at most M-1 such that p(x_i) = y_i for all i.

    The polynomial is given by the Lagrange formula:
    p(x) = Σ_i y_i * Π_{j≠i} (x - x_j) / (x_i - x_j)

    This uses Mathlib's Lagrange.interpolate function.
-/
theorem lagrange_interpolation_proof (M : Nat) (hM : M > 0)
    (points : Fin M -> Real)
    (values : Fin M -> Real)
    (hdistinct : ∀ i j, i ≠ j -> points i ≠ points j) :
    ∃ (p : Polynomial Real),
      p.natDegree < M ∧
      ∀ i : Fin M, p.eval (points i) = values i := by
  use Lagrange.interpolate Finset.univ points values
  constructor
  · -- Degree bound: natDegree < M
    -- Lagrange.degree_interpolate_lt shows degree < #s when v is injective on s
    have hinj : Set.InjOn points (Finset.univ : Finset (Fin M)) := by
      -- InjOn: ∀ a ∈ s, ∀ b ∈ s, points a = points b → a = b
      intro a _ b _ hab
      -- hab : points a = points b, need to show a = b
      by_contra hne
      -- hne : ¬(a = b) i.e. a ≠ b
      -- hdistinct says: a ≠ b → points a ≠ points b
      exact hdistinct a b hne hab
    have hdeg := @Lagrange.degree_interpolate_lt Real _ (Fin M) _
        Finset.univ points values hinj
    rw [Finset.card_fin] at hdeg
    -- Convert degree < M to natDegree < M
    by_cases hp : Lagrange.interpolate Finset.univ points values = 0
    · -- If polynomial is zero, natDegree = 0 < M
      simp [hp, hM]
    · -- If polynomial is nonzero, use natDegree_lt_iff_degree_lt
      exact (Polynomial.natDegree_lt_iff_degree_lt hp).mpr hdeg
  · -- Evaluation at points
    intro i
    have hinj : Set.InjOn points (Finset.univ : Finset (Fin M)) := by
      -- InjOn: ∀ a ∈ s, ∀ b ∈ s, points a = points b → a = b
      intro a _ b _ hab
      -- hab : points a = points b, need to show a = b
      by_contra hne
      -- hne : ¬(a = b) i.e. a ≠ b
      -- hdistinct says: a ≠ b → points a ≠ points b
      exact hdistinct a b hne hab
    -- Lagrange.eval_interpolate_at_node gives: eval (v i) (interpolate s v r) = r i
    -- Variables in Lagrange: {s : Finset ι} {i : ι} {v : ι → F} (r : ι → F)
    -- So @ order is: F, Field F, ι, DecidableEq ι, s, i, v, r, hvs, hi
    have h := @Lagrange.eval_interpolate_at_node Real _ (Fin M) _
        Finset.univ i points values hinj (Finset.mem_univ i)
    exact h

end UAQO.Complexity.Proofs
