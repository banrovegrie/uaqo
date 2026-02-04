/-
  Spectral theory for Hermitian operators.

  We define eigenvalues, eigenvectors, spectral decomposition, and the spectral gap.
-/
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Data.Real.Basic
import UAQO.Foundations.Operators

namespace UAQO

/-! ## Eigenvalues and eigenvectors -/

/-- An eigenvalue-eigenvector pair for operator A -/
structure EigenPair (N : Nat) where
  eigenvalue : Real  -- Hermitian operators have real eigenvalues
  eigenvector : Ket N
  normalized : normSquared eigenvector = 1

/-- A is an eigenvalue of A if Av = λv for some nonzero v -/
def IsEigenvalue {N : Nat} (A : Operator N) (lambda : Real) : Prop :=
  ∃ (v : Ket N), normSquared v > 0 ∧ applyOp A v = (lambda : Complex) • v

/-- The spectrum of an operator is the set of its eigenvalues -/
def Spectrum {N : Nat} (A : Operator N) : Set Real :=
  { lambda | IsEigenvalue A lambda }

/-! ## Spectral decomposition of Hermitian operators -/

/-- A spectral decomposition of a Hermitian operator with M distinct eigenvalues -/
structure SpectralDecomp (N M : Nat) (A : Operator N) where
  eigenvalues : Fin M -> Real
  degeneracies : Fin M -> Nat
  /-- The eigenprojectors for each eigenspace -/
  projectors : Fin M -> Operator N
  /-- Eigenvalues are ordered -/
  ordered : ∀ i j, i < j -> eigenvalues i < eigenvalues j
  /-- Degeneracies sum to N -/
  deg_sum : Finset.sum Finset.univ degeneracies = N
  /-- Each projector projects onto its eigenspace -/
  projector_rank : ∀ k, trace (projectors k) = degeneracies k
  /-- Projectors are orthogonal -/
  projector_orthogonal : ∀ i j, i ≠ j -> projectors i * projectors j = 0
  /-- Projectors sum to identity -/
  projector_complete : Finset.sum Finset.univ projectors = identityOp N
  /-- Spectral decomposition holds -/
  spectral_decomp : A = Finset.sum Finset.univ
    (fun k => (eigenvalues k : Complex) • projectors k)

/-! ## Spectral gap -/

/-- The spectral gap of an operator is the difference between its two smallest eigenvalues -/
noncomputable def spectralGap (N M : Nat) (A : Operator N)
    (sd : SpectralDecomp N M A) (hM : M >= 2) : Real :=
  sd.eigenvalues ⟨1, hM⟩ - sd.eigenvalues ⟨0, Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hM⟩

notation "Δ(" A ")" => spectralGap _ _ A

/-- The spectral gap is positive when there are at least 2 distinct eigenvalues -/
theorem spectralGap_pos (N M : Nat) (A : Operator N)
    (sd : SpectralDecomp N M A) (hM : M >= 2) :
    spectralGap N M A sd hM > 0 := by
  simp only [spectralGap]
  have h0 : 0 < M := Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hM
  have h := sd.ordered ⟨0, h0⟩ ⟨1, hM⟩
  simp only [Fin.mk_lt_mk] at h
  linarith [h (by norm_num : (0 : Nat) < 1)]

/-! ## Minimum eigenvalue (ground energy) -/

/-- The minimum eigenvalue of a Hermitian operator (requires M > 0) -/
noncomputable def groundEnergy (N M : Nat) (A : Operator N)
    (sd : SpectralDecomp N M A) (hM : M > 0) : Real :=
  sd.eigenvalues ⟨0, hM⟩

notation "E₀(" A ")" => groundEnergy _ _ A

/-! ## Infrastructure for variational principle -/

/-- Expectation value is linear in the operator for finite sums -/
lemma expectation_sum {N : Nat} (phi : Ket N) {M : Nat}
    (ops : Fin M → Operator N) :
    expectation (Finset.sum Finset.univ ops) phi =
    Finset.sum Finset.univ (fun k => expectation (ops k) phi) := by
  simp only [expectation, innerProd, applyOp]
  rw [Finset.sum_comm]
  congr 1
  ext i
  rw [Finset.sum_comm]
  congr 1
  ext j
  rw [Finset.sum_mul]
  congr 1
  ext k
  simp only [Matrix.sum_apply]
  ring

/-- Expectation value of a scalar multiple -/
lemma expectation_smul {N : Nat} (c : Complex) (A : Operator N) (phi : Ket N) :
    expectation (c • A) phi = c * expectation A phi := by
  simp only [expectation, innerProd, applyOp]
  rw [Finset.mul_sum]
  congr 1
  ext i
  rw [Finset.mul_sum]
  congr 1
  ext j
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

/-- Expectation value of identity is normSquared -/
lemma expectation_identity {N : Nat} (phi : Ket N) :
    expectation (identityOp N) phi = normSquared phi := by
  simp only [expectation, innerProd, applyOp, identityOp]
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_eq_single i]
    · simp only [Matrix.diagonal_apply_eq, one_mul]
    · intro j _ hji
      simp only [Matrix.diagonal_apply_ne _ (Ne.symm hji), zero_mul]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  rw [sum_star_mul_self_eq_normSquared]
  simp only [Complex.ofReal_re, normSquared]
  rfl

/-- Expectation value of identity (real part) -/
lemma expectation_identity_re {N : Nat} (phi : Ket N) :
    (expectation (identityOp N) phi).re = normSquared phi := by
  rw [expectation_identity]
  exact Complex.ofReal_re (normSquared phi)

/-- Hermitian operators have real expectation values -/
lemma hermitian_expectation_real {N : Nat} (A : Operator N)
    (hA : IsHermitian A) (phi : Ket N) :
    (expectation A phi).im = 0 := by
  -- ⟨φ|A|φ⟩* = ⟨Aφ|φ⟩ = ⟨φ|A†|φ⟩ = ⟨φ|A|φ⟩ (using A = A†)
  -- So the expectation equals its conjugate, hence is real
  simp only [expectation, innerProd, applyOp]
  -- Need to show Im(Σᵢ φᵢ* (Σⱼ Aᵢⱼ φⱼ)) = 0
  -- Key: A = A† means Aᵢⱼ = (Aⱼᵢ)*
  have hconj : ∀ i j, A i j = star (A j i) := by
    intro i j
    have h := hA
    unfold IsHermitian dagger at h
    have heq : A i j = A.conjTranspose i j := by rw [h]
    simp only [Matrix.conjTranspose_apply] at heq
    exact heq
  -- The sum Σᵢⱼ φᵢ* Aᵢⱼ φⱼ equals its conjugate
  -- Conjugate: Σᵢⱼ φᵢ (Aᵢⱼ)* φⱼ* = Σᵢⱼ φᵢ Aⱼᵢ φⱼ* = Σⱼᵢ φⱼ Aᵢⱼ φᵢ* (swap i,j)
  --          = Σᵢⱼ φⱼ* Aⱼᵢ φᵢ (using Aⱼᵢ = (Aᵢⱼ)*)
  -- This requires careful index manipulation
  -- Using Complex.im_eq_zero_iff_conj_eq_self
  rw [Complex.im_eq_zero_iff_conj_eq_self]
  simp only [map_sum, starRingEnd_self_apply]
  conv_rhs =>
    arg 2
    ext i
    rw [Finset.sum_mul]
    arg 2
    ext j
    rw [star_mul, star_star]
  rw [Finset.sum_comm]
  congr 1
  ext j
  rw [Finset.mul_sum]
  congr 1
  ext i
  rw [hconj i j, star_star]
  ring

/-- Inner product of Av with v equals inner product of v with A†v -/
lemma innerProd_applyOp_eq_applyOp_dagger {N : Nat} (A : Operator N) (v w : Ket N) :
    innerProd (applyOp A v) w = innerProd v (applyOp (A†) w) := by
  simp only [innerProd, applyOp, dagger]
  rw [Finset.sum_comm]
  congr 1
  ext j
  rw [Finset.sum_mul, Finset.mul_sum]
  congr 1
  ext i
  simp only [Matrix.conjTranspose_apply, conj_eq_star, star_eq_starRingEnd]
  ring

/-- For a projector P, ⟨φ|P|φ⟩ = ‖Pφ‖² -/
lemma projector_expectation_eq_normSquared {N : Nat} (P : Operator N)
    (hP : IsProjector P) (phi : Ket N) :
    expectation P phi = normSquared (applyOp P phi) := by
  -- Key: P = P† and P² = P, so ⟨φ|P|φ⟩ = ⟨φ|P†P|φ⟩ = ⟨Pφ|Pφ⟩ = ‖Pφ‖²
  have hHerm := hP.1
  have hIdem := hP.2
  simp only [expectation]
  -- ⟨φ|P|φ⟩ = ⟨Pφ|φ⟩ since P = P†
  -- But we want ⟨φ|P|φ⟩ = ⟨Pφ|Pφ⟩
  -- Use P² = P: ⟨φ|P|φ⟩ = ⟨φ|P²|φ⟩ = ⟨φ|P(Pφ)⟩
  -- And P = P†: ⟨φ|P(Pφ)⟩ = ⟨P†φ|Pφ⟩ = ⟨Pφ|Pφ⟩
  conv_lhs =>
    rw [show applyOp P phi = applyOp (P * P) phi by rw [hIdem]]
  -- applyOp (P * P) phi = applyOp P (applyOp P phi)
  have happly_mul : applyOp (P * P) phi = applyOp P (applyOp P phi) := by
    funext i
    simp only [applyOp, Matrix.mul_apply]
    rw [Finset.sum_comm]
    congr 1
    ext k
    rw [Finset.sum_mul]
    congr 1
    ext j
    ring
  rw [happly_mul]
  -- Now: innerProd phi (applyOp P (applyOp P phi))
  -- Use A = A†: innerProd phi (applyOp A v) = innerProd (applyOp A† phi) v
  -- With A = P and P† = P: innerProd phi (P(Pφ)) = innerProd (Pφ) (Pφ)
  rw [innerProd_applyOp_eq_applyOp_dagger P phi (applyOp P phi)]
  -- Now have: innerProd (applyOp P† phi) (applyOp P phi)
  -- Since P† = P (Hermitian):
  have hPdag : P† = P := by
    unfold IsHermitian at hHerm
    rw [hHerm]
  rw [hPdag]
  -- innerProd (applyOp P phi) (applyOp P phi) = ‖Pφ‖²
  rw [innerProd_self_eq_normSquared]

/-- For a projector P, ⟨φ|P|φ⟩ is real and non-negative.

    Proof: P is Hermitian and P² = P, so ⟨φ|P|φ⟩ = ‖Pφ‖² ≥ 0 -/
lemma projector_expectation_nonneg {N : Nat} (P : Operator N)
    (hP : IsProjector P) (phi : Ket N) :
    (expectation P phi).re >= 0 ∧ (expectation P phi).im = 0 := by
  constructor
  · -- Real part is non-negative
    rw [projector_expectation_eq_normSquared P hP phi]
    simp only [Complex.ofReal_re]
    exact normSquared_nonneg (applyOp P phi)
  · -- Imaginary part is zero (Hermitian)
    exact hermitian_expectation_real P hP.1 phi

/-- Ground energy is the minimum eigenvalue -/
lemma groundEnergy_le_eigenvalue {N M : Nat} (A : Operator N)
    (sd : SpectralDecomp N M A) (hM : M > 0) (k : Fin M) :
    groundEnergy N M A sd hM <= sd.eigenvalues k := by
  unfold groundEnergy
  by_cases hk : k.val = 0
  · simp only [Fin.val_eq_val] at hk
    have : k = ⟨0, hM⟩ := Fin.ext hk
    rw [this]
  · have hkpos : 0 < k.val := Nat.pos_of_ne_zero hk
    have hord := sd.ordered ⟨0, hM⟩ k (Fin.mk_lt_mk.mpr hkpos)
    linarith

/-- Sum of projector expectations equals expectation of their sum -/
lemma sum_projector_expectations {N M : Nat} (phi : Ket N)
    (projectors : Fin M → Operator N) :
    Finset.sum Finset.univ (fun k => expectation (projectors k) phi) =
    expectation (Finset.sum Finset.univ projectors) phi := by
  rw [expectation_sum]

/-- For a complete set of projectors, Σ_k ⟨φ|P_k|φ⟩ = ⟨φ|I|φ⟩ -/
lemma complete_projectors_sum_expectation {N M : Nat} (phi : Ket N)
    (projectors : Fin M → Operator N)
    (hcomplete : Finset.sum Finset.univ projectors = identityOp N) :
    Finset.sum Finset.univ (fun k => expectation (projectors k) phi) =
    expectation (identityOp N) phi := by
  rw [sum_projector_expectations, hcomplete]

/-- For a complete set of projectors and normalized phi, Σ_k Re⟨φ|P_k|φ⟩ = 1 -/
lemma complete_projectors_sum_re {N M : Nat} (phi : Ket N)
    (hphi : normSquared phi = 1)
    (projectors : Fin M → Operator N)
    (hcomplete : Finset.sum Finset.univ projectors = identityOp N) :
    Finset.sum Finset.univ (fun k => (expectation (projectors k) phi).re) = 1 := by
  have h := complete_projectors_sum_expectation phi projectors hcomplete
  -- Re of sum = sum of Re when all are real
  -- First show Σ_k exp_k = exp_I
  rw [← h, expectation_identity, hphi]
  -- Now: Σ_k Re(exp_k) = Re(1) = 1
  -- Need: Re(Σ_k exp_k) = Σ_k Re(exp_k)
  simp only [Complex.ofReal_one, Complex.one_re]
  rw [← Complex.re_sum]
  congr 1

/-- Weighted sum bound: if w_k ≥ 0, Σ w_k = 1, and a_k ≥ a_0, then Σ a_k w_k ≥ a_0 -/
lemma weighted_sum_ge_min {M : Nat} (a : Fin M → Real) (w : Fin M → Real)
    (hw_nonneg : ∀ k, w k >= 0)
    (hw_sum : Finset.sum Finset.univ w = 1)
    (a0 : Real) (ha_ge : ∀ k, a k >= a0) :
    Finset.sum Finset.univ (fun k => a k * w k) >= a0 := by
  calc Finset.sum Finset.univ (fun k => a k * w k)
      >= Finset.sum Finset.univ (fun k => a0 * w k) := by
        apply Finset.sum_le_sum
        intro k _
        have h1 : a k >= a0 := ha_ge k
        have h2 : w k >= 0 := hw_nonneg k
        nlinarith
    _ = a0 * Finset.sum Finset.univ w := by rw [← Finset.mul_sum]
    _ = a0 * 1 := by rw [hw_sum]
    _ = a0 := by ring

/-! ## Variational principle -/

/-- The variational principle: ⟨φ|A|φ⟩ ≥ E₀ for any normalized state φ.

    This is a fundamental result in spectral theory stating that the expectation
    value of a Hermitian operator is bounded below by its smallest eigenvalue.

    Proof outline using spectral decomposition A = Σ_k E_k P_k:
    1. ⟨φ|A|φ⟩ = Σ_k E_k ⟨φ|P_k|φ⟩           (linearity)
    2. Let c_k = ⟨φ|P_k|φ⟩ ≥ 0               (projector positivity)
    3. Σ_k c_k = ⟨φ|I|φ⟩ = 1                 (projector completeness, normalization)
    4. Σ_k E_k c_k ≥ E_0 Σ_k c_k = E_0       (E_0 ≤ E_k and c_k ≥ 0) -/
theorem variational_principle (N M : Nat) (A : Operator N)
    (sd : SpectralDecomp N M A) (hM : M > 0) (phi : Ket N)
    (hphi : normSquared phi = 1) :
    (expectation A phi).re >= groundEnergy N M A sd hM := by
  -- Use spectral decomposition: A = Σ_k E_k • P_k
  have hdecomp := sd.spectral_decomp
  rw [hdecomp]
  -- Expectation of sum = sum of expectations
  rw [expectation_sum]
  -- Each term is E_k * ⟨φ|P_k|φ⟩
  conv_lhs =>
    arg 2
    ext k
    rw [expectation_smul]
  -- Need: Re(Σ_k (E_k : ℂ) * ⟨φ|P_k|φ⟩) ≥ E_0
  -- Key facts:
  -- 1. ⟨φ|P_k|φ⟩ is real and ≥ 0 (projector positivity)
  -- 2. E_k ≥ E_0 for all k (eigenvalue ordering)
  -- 3. Σ_k ⟨φ|P_k|φ⟩ = 1 (completeness + normalization)
  sorry  -- Full proof requires projector_expectation_nonneg without sorry

/-- The minimum is achieved by the ground state.

    There exists a normalized eigenstate achieving the ground energy.
    Construction: Take any unit vector in the ground eigenspace (range of P_0).
    Since degeneracies k > 0 implies P_k has positive rank, such a vector exists. -/
theorem variational_minimum (N M : Nat) (A : Operator N)
    (sd : SpectralDecomp N M A) (hM : M > 0) :
    ∃ (psi : Ket N), normSquared psi = 1 ∧
      (expectation A psi).re = groundEnergy N M A sd hM := by
  -- The ground projector P_0 has rank = d_0 > 0
  -- Take any unit vector in its range
  -- For such ψ: P_0|ψ⟩ = |ψ⟩ and P_k|ψ⟩ = 0 for k ≠ 0
  -- So ⟨ψ|A|ψ⟩ = E_0 ⟨ψ|P_0|ψ⟩ = E_0 · 1 = E_0
  sorry  -- Requires extracting unit vector from projector range

end UAQO
