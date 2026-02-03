/-
  Hilbert space foundations for quantum mechanics.

  We work with finite-dimensional complex Hilbert spaces represented as
  Complex^N where N = 2^n for n qubits.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Topology.MetricSpace.Basic
import UAQO.Foundations.Basic

namespace UAQO

/-! ## Finite-dimensional Hilbert spaces -/

/-- A quantum state in an N-dimensional Hilbert space is a unit vector in Complex^N -/
structure QuantumState (N : Nat) [NeZero N] where
  vec : Fin N -> Complex
  normalized : Finset.sum Finset.univ (fun i => Complex.normSq (vec i)) = 1

/-- The inner product of two vectors -/
noncomputable def innerProd {N : Nat} (v w : Fin N -> Complex) : Complex :=
  Finset.sum Finset.univ (fun i => conj (v i) * w i)

notation "⟪" v ", " w "⟫" => innerProd v w

/-- Inner product is conjugate symmetric -/
theorem innerProd_conj_symm {N : Nat} (v w : Fin N -> Complex) :
    innerProd v w = conj (innerProd w v) := by
  simp only [innerProd, conj]
  rw [map_sum (starRingEnd Complex)]
  congr 1
  ext i
  rw [(starRingEnd Complex).map_mul, starRingEnd_self_apply]
  ring

/-- The norm squared of a vector -/
noncomputable def normSquared {N : Nat} (v : Fin N -> Complex) : Real :=
  Finset.sum Finset.univ (fun i => Complex.normSq (v i))

notation "‖" v "‖²" => normSquared v

/-- Norm squared is non-negative -/
theorem normSquared_nonneg {N : Nat} (v : Fin N -> Complex) : normSquared v >= 0 := by
  apply Finset.sum_nonneg
  intro i _
  exact Complex.normSq_nonneg (v i)

/-- Bra-ket notation: |v⟩ is a ket (column vector) -/
abbrev Ket (N : Nat) := Fin N -> Complex

/-- Bra-ket notation: ⟨v| is a bra (conjugate transpose) -/
noncomputable def Bra {N : Nat} (v : Fin N -> Complex) : Fin N -> Complex :=
  fun i => conj (v i)

notation "|" v "⟩" => v
notation "⟨" v "|" => Bra v

/-- The outer product |v⟩⟨w| -/
noncomputable def outerProd {N : Nat} (v w : Fin N -> Complex) : Matrix (Fin N) (Fin N) Complex :=
  Matrix.of (fun i j => v i * conj (w j))

notation "|" v "⟩⟨" w "|" => outerProd v w

/-- The computational basis state |k⟩ -/
noncomputable def compBasisState (N : Nat) [NeZero N] (k : Fin N) : Fin N -> Complex :=
  fun i => if i = k then 1 else 0

/-- Computational basis states are orthonormal.
    Proof: ⟨j|k⟩ = Σᵢ δᵢⱼ δᵢₖ = δⱼₖ -/
theorem compBasis_orthonormal (N : Nat) [NeZero N] (j k : Fin N) :
    innerProd (compBasisState N j) (compBasisState N k) = if j = k then 1 else 0 := by
  simp only [innerProd, compBasisState]
  by_cases hjk : j = k
  · subst hjk
    simp only [ite_true]
    rw [Finset.sum_eq_single j]
    · simp [conj]
    · intro i _ hij
      simp [hij]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  · simp only [hjk, ite_false]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hij : i = j
    · subst hij
      simp only [ite_true, hjk, ite_false, mul_zero]
    · simp only [hij, ite_false, conj, map_zero, zero_mul]

/-- The equal superposition state |ψ₀⟩ = (1/√N) Σ |k⟩ -/
noncomputable def equalSuperposition (N : Nat) [NeZero N] : Fin N -> Complex :=
  fun _ => (1 : Complex) / Complex.ofReal (Real.sqrt N)

notation "|ψ₀⟩" => equalSuperposition

/-- Equal superposition is normalized when N > 0.
    Proof: Σᵢ |1/√N|² = N · (1/N) = 1 -/
theorem equalSuperposition_normalized (N : Nat) [NeZero N] (hN : (N : Real) > 0) :
    normSquared (equalSuperposition N) = 1 := by
  simp only [normSquared, equalSuperposition]
  rw [Finset.sum_const, Finset.card_fin]
  simp only [nsmul_eq_mul]
  rw [Complex.normSq_div, Complex.normSq_one, Complex.normSq_ofReal]
  rw [Real.mul_self_sqrt (le_of_lt hN)]
  field_simp

end UAQO
