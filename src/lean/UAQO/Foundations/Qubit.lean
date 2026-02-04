/-
  Qubit systems and tensor product structure.

  We define n-qubit systems, the computational basis, and tensor products.
-/
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import UAQO.Foundations.SpectralTheory

namespace UAQO

/-! ## Single qubit -/

/-- The dimension of an n-qubit system -/
def qubitDim (n : Nat) : Nat := 2^n

instance qubitDim_neZero (n : Nat) : NeZero (qubitDim n) :=
  ⟨Nat.ne_of_gt (Nat.pow_pos (by norm_num : 0 < 2))⟩

/-- A qubit is a 2-dimensional quantum system -/
abbrev Qubit := Ket 2

/-- The |0⟩ state -/
noncomputable def ket0 : Qubit := compBasisState 2 ⟨0, by norm_num⟩

/-- The |1⟩ state -/
noncomputable def ket1 : Qubit := compBasisState 2 ⟨1, by norm_num⟩

/-- ket0 is normalized -/
lemma normSquared_ket0 : normSquared ket0 = 1 := by
  simp only [normSquared, ket0, compBasisState]
  rw [Fin.sum_univ_two]
  simp [Complex.normSq_one, Complex.normSq_zero]

/-- ket1 is normalized -/
lemma normSquared_ket1 : normSquared ket1 = 1 := by
  simp only [normSquared, ket1, compBasisState]
  rw [Fin.sum_univ_two]
  simp [Complex.normSq_one, Complex.normSq_zero]

/-- The |+⟩ state = (|0⟩ + |1⟩)/√2 -/
noncomputable def ketPlus : Qubit :=
  fun _ => 1 / Complex.ofReal (Real.sqrt 2)

/-- The |-⟩ state = (|0⟩ - |1⟩)/√2 -/
noncomputable def ketMinus : Qubit :=
  fun i => if i.val = 0 then 1 / Complex.ofReal (Real.sqrt 2)
           else -1 / Complex.ofReal (Real.sqrt 2)

/-! ## n-qubit systems -/

/-- An n-qubit state -/
abbrev NQubitState (n : Nat) := Ket (qubitDim n)

/-- An n-qubit operator -/
abbrev NQubitOperator (n : Nat) := Operator (qubitDim n)

/-- The computational basis state |z⟩ for bitstring z ∈ {0,1}ⁿ -/
noncomputable def compBasisFromBitstring (n : Nat) (z : Fin (qubitDim n)) :
    NQubitState n :=
  compBasisState (qubitDim n) z

/-- The equal superposition state |ψ₀⟩ = |+⟩^⊗n = (1/√N) Σ_z |z⟩ -/
noncomputable def equalSuperpositionN (n : Nat) : NQubitState n :=
  equalSuperposition (qubitDim n)

notation "|ψ₀^" n "⟩" => equalSuperpositionN n

/-- The initial Hamiltonian H₀ = -|ψ₀⟩⟨ψ₀| -/
noncomputable def initialHamiltonian (n : Nat) : NQubitOperator n :=
  (-1 : Complex) • projectorOnState (equalSuperpositionN n)

notation "H₀^" n => initialHamiltonian n

/-- The equal superposition is normalized -/
lemma equalSuperpositionN_normalized (n : Nat) :
    normSquared (equalSuperpositionN n) = 1 := by
  simp only [equalSuperpositionN]
  apply equalSuperposition_normalized
  simp only [qubitDim]
  exact Nat.cast_pos.mpr (Nat.pow_pos (by norm_num : 0 < 2))

/-- H₀ has ground energy -1 with ground state |ψ₀⟩ -/
theorem initialHam_groundState (n : Nat) :
    applyOp (initialHamiltonian n) (equalSuperpositionN n) =
    (-1 : Complex) • equalSuperpositionN n := by
  simp only [initialHamiltonian]
  rw [applyOp_smul]
  rw [applyOp_projector_self _ (equalSuperpositionN_normalized n)]

/-! ## Pauli matrices -/

/-- The Pauli X matrix -/
noncomputable def pauliX : Operator 2 :=
  !![0, 1; 1, 0]

/-- The Pauli Y matrix -/
noncomputable def pauliY : Operator 2 :=
  !![0, -Complex.I; Complex.I, 0]

/-- The Pauli Z matrix -/
noncomputable def pauliZ : Operator 2 :=
  !![1, 0; 0, -1]

notation "σₓ" => pauliX
notation "σᵧ" => pauliY
notation "σᵤ" => pauliZ

/-- Pauli Z eigenvalues -/
theorem pauliZ_eigenvalues :
    IsEigenvalue pauliZ 1 ∧ IsEigenvalue pauliZ (-1) := by
  constructor
  · -- Eigenvalue 1 with eigenvector ket0
    use ket0
    constructor
    · rw [normSquared_ket0]; norm_num
    · ext i
      fin_cases i <;> simp [applyOp, pauliZ, ket0, compBasisState]
  · -- Eigenvalue -1 with eigenvector ket1
    use ket1
    constructor
    · rw [normSquared_ket1]; norm_num
    · ext i
      fin_cases i <;> simp [applyOp, pauliZ, ket1, compBasisState]

/-! ## Bitstring indexing utilities -/

/-- The sum of powers of 2 equals 2^n - 1 (geometric series) -/
lemma geom_sum_eq_pow_sub_one (n : Nat) :
    Finset.sum Finset.univ (fun i : Fin n => (2 : Nat)^i.val) = 2^n - 1 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, Fin.val_succ]
    have h1 : Finset.sum Finset.univ (fun i : Fin k => 2^(i.val + 1)) =
              2 * Finset.sum Finset.univ (fun i : Fin k => 2^i.val) := by
      simp only [pow_succ, mul_comm]
      rw [← Finset.mul_sum]
    rw [h1, ih]
    have h : 2^k >= 1 := Nat.one_le_pow k 2 (by norm_num)
    omega

/-- Bitstring sum is bounded by 2^n -/
lemma bitstring_sum_bound (n : Nat) (bits : Fin n -> Bool) :
    Finset.sum Finset.univ (fun i : Fin n => if bits i then 2^i.val else 0) < 2^n := by
  calc Finset.sum Finset.univ (fun i : Fin n => if bits i then 2^i.val else 0)
      <= Finset.sum Finset.univ (fun i : Fin n => 2^i.val) := by
          apply Finset.sum_le_sum; intro i _; split_ifs <;> simp
      _ = 2^n - 1 := geom_sum_eq_pow_sub_one n
      _ < 2^n := Nat.sub_lt (Nat.one_le_pow n 2 (by norm_num)) (by norm_num)

/-- Convert a natural number to an n-bit bitstring -/
def natToBitstring (n : Nat) (k : Fin (2^n)) : Fin n -> Bool :=
  fun i => (k.val / 2^i.val) % 2 = 1

/-- Convert an n-bit bitstring to a natural number -/
def bitstringToNat (n : Nat) (bits : Fin n -> Bool) : Fin (2^n) :=
  ⟨Finset.sum Finset.univ (fun i => if bits i then 2^i.val else 0),
   bitstring_sum_bound n bits⟩

end UAQO
