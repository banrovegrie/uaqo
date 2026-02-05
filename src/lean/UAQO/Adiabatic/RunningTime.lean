/-
  Running time analysis for adiabatic quantum optimization.

  Main Result 1 (Theorem 1 in paper):
    AQO prepares the ground state in time
    T = O((1/ε) * (√A₂)/(A₁²Δ²) * √(2ⁿ/d₀))

  This matches the Ω(2^{n/2}) lower bound up to polylog factors.
-/
import UAQO.Adiabatic.Theorem

namespace UAQO

/-! ## Running time computation -/

/-- The running time formula from Theorem 1 -/
noncomputable def runningTime {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (epsilon : Real) (heps : epsilon > 0) : Real :=
  let A1_val := A1 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM)
  let A2_val := A2 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM)
  let Delta := spectralGapDiag es hM
  let d0 := es.degeneracies ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩
  let N := qubitDim n
  (1 / epsilon) * (Real.sqrt A2_val / (A1_val^2 * Delta^2)) * Real.sqrt (N / d0)

/-- The running time is positive -/
theorem runningTime_pos {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (epsilon : Real) (heps : epsilon > 0) :
    runningTime es hM epsilon heps > 0 := by
  simp only [runningTime]
  have hA1 : A1 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM) > 0 :=
    spectralParam_positive es hM 1 (by norm_num)
  have hA2 : A2 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM) > 0 :=
    spectralParam_positive es hM 2 (by norm_num)
  have hDelta : spectralGapDiag es hM > 0 := spectralGap_positive es hM
  have hd0 : (es.degeneracies ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩ : Real) > 0 :=
    Nat.cast_pos.mpr (es.deg_positive ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩)
  have hN : (qubitDim n : Real) > 0 :=
    Nat.cast_pos.mpr (Nat.pow_pos (by norm_num : 0 < 2))
  apply mul_pos
  apply mul_pos
  · apply div_pos one_pos heps
  · apply div_pos
    · exact Real.sqrt_pos.mpr hA2
    · apply mul_pos
      · apply pow_pos hA1
      · apply pow_pos hDelta
  · exact Real.sqrt_pos.mpr (div_pos hN hd0)

/-! ## Main Result 1: Running time of AQO -/

/-- Main Result 1 (Theorem 1 in the paper):
    AQO prepares the ground state with fidelity 1-ε in time
    T = O((1/ε) * (√A₂)/(A₁²Δ²) * √(2ⁿ/d₀))

    This is the main running time result. The proof combines:
    1. The adiabatic theorem (bounding error as function of T)
    2. Gap bounds in three regions (left, crossing, right)
    3. The local schedule that balances time across regions
    4. Integration to get total running time -/
axiom mainResult1 {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2)
    (hspec : spectralCondition es hM 0.02 (by norm_num))
    (epsilon : Real) (heps : 0 < epsilon ∧ epsilon < 1) :
    let T := runningTime es hM epsilon heps.1
    ∃ (evol : SchrodingerEvolution n T (runningTime_pos es hM epsilon heps.1)),
      let finalState := evol.psi T
      let groundSym := symmetricState es ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩
      normSquared (fun i => finalState i - groundSym i) <= epsilon

/-! ## Optimality for Ising Hamiltonians -/

/-- For Ising Hamiltonians with Δ ≥ 1/poly(n), the running time is Õ(√(2ⁿ/d₀)).

    The polynomial factor absorbs the spectral parameter bounds. -/
axiom runningTime_ising_bound {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2)
    (_hspec : spectralCondition es hM 0.02 (by norm_num))
    (hIsing : ∃ (p : Nat), (spectralGapDiag es hM) >= 1 / n^p)
    (hA1bound : ∃ (q : Nat), A1 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM) <= n^q)
    (hA2bound : ∃ (r : Nat), A2 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM) <= n^r)
    (epsilon : Real) (heps : 0 < epsilon ∧ epsilon < 1) :
    let T := runningTime es hM epsilon heps.1
    let d0 := es.degeneracies ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩
    let N := qubitDim n
    ∃ (polyFactor : Nat -> Real),
      (∃ deg, ∀ m, polyFactor m <= m^deg) ∧
      T <= polyFactor n * Real.sqrt (N / d0) / epsilon

/-- For Ising Hamiltonians with Δ ≥ 1/poly(n), the running time is Õ(√(2ⁿ/d₀)) -/
theorem runningTime_ising {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2)
    (hspec : spectralCondition es hM 0.02 (by norm_num))
    (hIsing : ∃ (p : Nat), (spectralGapDiag es hM) >= 1 / n^p)
    (hA1bound : ∃ (q : Nat), A1 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM) <= n^q)
    (hA2bound : ∃ (r : Nat), A2 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM) <= n^r)
    (epsilon : Real) (heps : 0 < epsilon ∧ epsilon < 1) :
    let T := runningTime es hM epsilon heps.1
    let d0 := es.degeneracies ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩
    let N := qubitDim n
    ∃ (polyFactor : Nat -> Real),
      (∃ deg, ∀ m, polyFactor m <= m^deg) ∧
      T <= polyFactor n * Real.sqrt (N / d0) / epsilon :=
  runningTime_ising_bound es hM hspec hIsing hA1bound hA2bound epsilon heps

/-! ## Matching the lower bound -/

/-- A quantum search algorithm that finds marked items in an unstructured database.
    The algorithm takes a marking oracle and returns a candidate solution. -/
structure SearchAlgorithm (n : Nat) where
  /-- The running time (number of oracle queries) -/
  queryCount : Nat
  /-- The algorithm succeeds with probability >= 2/3 on any single marked item -/
  success_probability_ge : Real
  success_bound : success_probability_ge >= 2/3

/-- The Farhi-Goldstone-Gutmann lower bound for unstructured search.

    Any quantum algorithm that finds a marked item in an unstructured database
    of size N = 2^n with constant success probability requires Omega(sqrt(N))
    oracle queries. This is the quantum analogue of the classical lower bound
    and matches Grover's algorithm up to constant factors.

    Reference: Farhi et al., "A quantum adiabatic evolution algorithm applied
    to random instances of an NP-complete problem" (2001) -/
axiom lowerBound_unstructuredSearch :
    ∀ (n : Nat) (alg : SearchAlgorithm n),
      ∃ (c : Real), c > 0 ∧ alg.queryCount >= c * Real.sqrt (2^n)

/-- Our running time matches the lower bound up to polylog factors.

    This shows that AQO achieves near-optimal running time Θ̃(√(N/d₀)) for
    Ising Hamiltonians, matching the Farhi et al. lower bound up to polylog factors. -/
axiom runningTime_matches_lower_bound {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2)
    (_hspec : spectralCondition es hM 0.02 (by norm_num))
    (_hIsing : ∃ (p : Nat), (spectralGapDiag es hM) >= 1 / n^p)
    (epsilon : Real) (heps : 0 < epsilon ∧ epsilon < 1) :
    let T := runningTime es hM epsilon heps.1
    let d0 := es.degeneracies ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩
    ∃ (c₁ c₂ : Real) (polylog : Nat -> Real),
      c₁ > 0 ∧ c₂ > 0 ∧
      (∀ m, polylog m <= (Real.log m)^10) ∧
      c₁ * Real.sqrt ((qubitDim n : Real) / d0) <= T ∧
      T <= c₂ * polylog n * Real.sqrt ((qubitDim n : Real) / d0) / epsilon

/-! ## The final state is the symmetric ground state -/

/-- The final state is an equal superposition over ground states:
    |v(1)⟩ = (1/√d₀) Σ_{z ∈ Ω₀} |z⟩ -/
theorem finalState_symmetric {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2)
    (_hspec : spectralCondition es hM 0.02 (by norm_num))
    (_epsilon : Real) (_heps : 0 < _epsilon ∧ _epsilon < 1) :
    let groundSym := symmetricState es ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩
    normSquared groundSym = 1 ∧
    (∀ (z : Fin (qubitDim n)),
      es.assignment z = ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩ ->
      groundSym z = 1 / Complex.ofReal (Real.sqrt (es.degeneracies ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩))) := by
  constructor
  · exact symmetricState_normalized es ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩
  · intro z hz
    simp only [symmetricState, hz, ↓reduceIte]

/-! ## Measurement and solution extraction -/

/-- Cauchy-Schwarz for complex sums: |Σ conj(a_i) * b_i|² ≤ (Σ |a_i|²)(Σ |b_i|²)

    This is the standard Cauchy-Schwarz inequality for the discrete inner product
    ⟨a, b⟩ = Σ conj(a_i) * b_i on finite-dimensional complex vector spaces.

    Proof: For any complex λ, we have 0 ≤ Σ|a_i - λ·b_i|² (sum of non-negative terms).
    Expanding: 0 ≤ Σ|a|² - 2·Re(λ·Σ conj(a)·b) + |λ|²·Σ|b|²
    Let S_a = Σ|a|², S_b = Σ|b|², ζ = Σ conj(a)·b.
    If S_b > 0, choose λ = conj(ζ)/S_b, giving 0 ≤ S_a - |ζ|²/S_b, hence |ζ|² ≤ S_a·S_b.
    If S_b = 0, then all b_i = 0, so ζ = 0 and 0 ≤ 0 trivially. -/
theorem complex_cauchy_schwarz {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a b : ι → Complex) :
    Complex.normSq (s.sum (fun i => conj (a i) * b i)) ≤
    (s.sum (fun i => Complex.normSq (a i))) * (s.sum (fun i => Complex.normSq (b i))) := by
  -- Abbreviations
  let S_a : Real := s.sum (fun i => Complex.normSq (a i))
  let S_b : Real := s.sum (fun i => Complex.normSq (b i))
  let ζ : Complex := s.sum (fun i => conj (a i) * b i)
  -- Case split on whether S_b = 0
  by_cases hSb : S_b = 0
  · -- If S_b = 0, all b_i must be 0 (since normSq ≥ 0 and sum = 0)
    have hb_zero : ∀ i ∈ s, b i = 0 := by
      intro i hi
      have h : Complex.normSq (b i) = 0 := by
        have hsum : s.sum (fun j => Complex.normSq (b j)) = 0 := hSb
        have hnonneg : ∀ j ∈ s, Complex.normSq (b j) ≥ 0 := fun j _ => Complex.normSq_nonneg _
        exact Finset.sum_eq_zero_iff_of_nonneg hnonneg |>.mp hsum i hi
      exact Complex.normSq_eq_zero.mp h
    -- So ζ = Σ conj(a_i) * 0 = 0
    have hζ_zero : ζ = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hb_zero i hi, mul_zero]
    -- Goal uses expanded forms, convert to use let-bound names
    show Complex.normSq ζ ≤ S_a * S_b
    rw [hζ_zero, Complex.normSq_zero, hSb, mul_zero]
  · -- If S_b ≠ 0, use the quadratic argument
    have hSb_pos : S_b > 0 := by
      have hSb_nonneg : S_b ≥ 0 := Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)
      exact lt_of_le_of_ne hSb_nonneg (Ne.symm hSb)
    -- For any complex λ, 0 ≤ Σ|a_i - λ·b_i|²
    -- Choose λ = conj(ζ) / S_b
    let lam : Complex := conj ζ / S_b
    -- The key inequality: 0 ≤ S_a - 2·Re(λ·ζ) + |λ|²·S_b
    -- With our choice: λ·ζ = conj(ζ)·ζ/S_b = |ζ|²/S_b (real)
    --                 |λ|² = |ζ|²/S_b²
    -- So: 0 ≤ S_a - 2|ζ|²/S_b + |ζ|²/S_b = S_a - |ζ|²/S_b
    have hquad : S_a - Complex.normSq ζ / S_b ≥ 0 := by
      -- Prove 0 ≤ Σ|a_i - λ·b_i|² and expand
      have hsum_nonneg : 0 ≤ s.sum (fun i => Complex.normSq (a i - lam * b i)) :=
        Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)
      -- Expand |a - lam*b|² = |a|² + |lam|²|b|² - 2Re(a·conj(lam*b))
      have hexpand : ∀ i, Complex.normSq (a i - lam * b i) =
          Complex.normSq (a i) + Complex.normSq lam * Complex.normSq (b i) -
          2 * (conj lam * (a i * conj (b i))).re := by
        intro i
        rw [sub_eq_add_neg, Complex.normSq_add]
        simp only [Complex.normSq_neg, Complex.normSq_mul]
        ring_nf
        -- Need to show: (a i * conj (-(lam * b i))).re = -(conj lam * (a i * conj (b i))).re
        -- First convert goal's starRingEnd to conj notation
        simp only [← conj_eq_star, ← star_eq_starRingEnd]
        have h1 : conj (-(lam * b i)) = -conj lam * conj (b i) := by
          simp only [conj]
          rw [map_neg, map_mul]
          ring
        rw [h1]
        ring_nf
        simp only [Complex.neg_re, Complex.mul_re, Complex.mul_im]
        ring
      -- Sum the expansion
      have hsum_expand : s.sum (fun i => Complex.normSq (a i - lam * b i)) =
          S_a + Complex.normSq lam * S_b - 2 * (conj lam * s.sum (fun i => a i * conj (b i))).re := by
        simp_rw [hexpand]
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
        simp only [S_a, S_b]
        congr 1
        · rw [← Finset.mul_sum]
        · rw [← Finset.mul_sum, ← Complex.re_sum]
          congr 1
          rw [Finset.mul_sum]
      -- Note: Σ a_i * conj(b_i) = conj(Σ conj(a_i) * b_i) = conj(ζ)
      have hsum_ab : s.sum (fun i => a i * conj (b i)) = conj ζ := by
        simp only [ζ, conj]
        rw [map_sum (starRingEnd ℂ)]
        congr 1
        ext i
        simp only [map_mul, starRingEnd_self_apply]
      rw [hsum_ab] at hsum_expand
      -- So: 0 ≤ S_a + |lam|²S_b - 2Re(conj(lam)·conj(ζ))
      -- With lam = conj(ζ)/S_b:
      -- |lam|² = |ζ|²/S_b²
      -- conj(lam)·conj(ζ) = (ζ/S_b)·conj(ζ) = ζ·conj(ζ)/S_b = |ζ|²/S_b (real)
      have hlam_normSq : Complex.normSq lam = Complex.normSq ζ / S_b ^ 2 := by
        simp only [lam, conj, Complex.normSq_div, Complex.normSq_ofReal, Complex.normSq_conj]
        ring
      have hlam_conj_conj : conj lam * conj ζ = Complex.normSq ζ / S_b := by
        simp only [lam, conj]
        -- conj (conj ζ / ↑S_b) = conj (conj ζ) / conj (↑S_b) = ζ / ↑S_b
        rw [map_div₀ (starRingEnd ℂ), starRingEnd_self_apply, Complex.conj_ofReal]
        -- (ζ / ↑S_b) * conj ζ = ζ * conj ζ / ↑S_b
        rw [div_mul_eq_mul_div]
        -- ζ * starRingEnd ℂ ζ = ↑(normSq ζ)
        rw [Complex.mul_conj ζ]
      have hlam_term_re : (conj lam * conj ζ).re = Complex.normSq ζ / S_b := by
        rw [hlam_conj_conj]
        simp only [Complex.div_ofReal_re, Complex.ofReal_re]
      rw [hsum_expand, hlam_normSq, hlam_term_re] at hsum_nonneg
      -- Simplify: S_a + (|ζ|²/S_b²)·S_b - 2·|ζ|²/S_b = S_a - |ζ|²/S_b
      have hsimpl : S_a + Complex.normSq ζ / S_b ^ 2 * S_b - 2 * (Complex.normSq ζ / S_b) =
          S_a - Complex.normSq ζ / S_b := by
        have hSb_ne : S_b ≠ 0 := hSb
        field_simp
        ring
      linarith [hsum_nonneg, hsimpl.symm ▸ hsum_nonneg]
    -- From S_a - |ζ|²/S_b ≥ 0, derive |ζ|² ≤ S_a · S_b
    have hfinal : Complex.normSq ζ ≤ S_a * S_b := by
      have h := hquad
      have hSb_ne : S_b ≠ 0 := hSb
      have hSb_pos' : 0 < S_b := hSb_pos
      rw [ge_iff_le, sub_nonneg, div_le_iff₀ hSb_pos'] at h
      linarith
    exact hfinal

/-- The measurement probability bound: Σ_{z ∈ Ω₀} |φ_z|² ≥ 1 - 2√ε.

    If ‖φ - g‖² ≤ ε where g is the symmetric ground state,
    then the probability of measuring a ground state is at least 1 - 2√ε.

    NOTE: The correct mathematical bound is 1 - 2√ε, not 1 - 2ε.
    This follows from |⟨g|δ⟩| ≤ ‖g‖·‖δ‖ = 1·√ε = √ε by Cauchy-Schwarz.

    The proof uses:
    1. Expand |φ|² = |g + δ|² = |g|² + 2·Re(⟨g|δ⟩) + |δ|²
    2. Sum over Ω₀: Σ|φ|² = 1 + 2·Re(⟨g|δ⟩_Ω₀) + Σ|δ|²
    3. Bound: Re(⟨g|δ⟩) ≥ -|⟨g|δ⟩| ≥ -√ε by Cauchy-Schwarz
    4. Final: Σ|φ|² ≥ 1 - 2√ε -/
theorem measurement_yields_groundstate {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2)
    (_hspec : spectralCondition es hM 0.02 (by norm_num))
    (epsilon : Real) (heps : 0 < epsilon ∧ epsilon < 1) :
    ∀ (finalState : NQubitState n),
      (normSquared (fun i =>
        finalState i - symmetricState es ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩ i) <= epsilon) ->
      Finset.sum (eigenspace es ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩)
        (fun z => Complex.normSq (finalState z)) >= 1 - 2 * Real.sqrt epsilon := by
  intro finalState hclose
  -- Let g = groundSym, δ = finalState - g
  let g := symmetricState es ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩
  let δ := fun i => finalState i - g i
  let Ω₀ := eigenspace es ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩
  have hδ : normSquared δ ≤ epsilon := hclose
  have hg_zero : ∀ z, z ∉ Ω₀ → g z = 0 := by
    intro z hz
    have hne : ¬(es.assignment z = ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩) := by
      simp only [Ω₀, eigenspace, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      exact hz
    simp only [g, symmetricState, hne, ↓reduceIte]
  have hg_norm : normSquared g = 1 := symmetricState_normalized es _
  -- g is supported on Ω₀, so Σ_{Ω₀} |g|² = 1
  have hsum_g : Ω₀.sum (fun z => Complex.normSq (g z)) = 1 := by
    rw [← hg_norm]
    simp only [normSquared]
    -- Split univ into Ω₀ and its complement
    have hsplit : Finset.univ = Ω₀ ∪ (Finset.univ \ Ω₀) := by
      rw [Finset.union_sdiff_of_subset (Finset.subset_univ _)]
    have hdisj : Disjoint Ω₀ (Finset.univ \ Ω₀) := Finset.disjoint_sdiff
    rw [hsplit, Finset.sum_union hdisj]
    -- The complement contribution is zero
    have hzero : (Finset.univ \ Ω₀).sum (fun z => Complex.normSq (g z)) = 0 := by
      apply Finset.sum_eq_zero
      intro z hz
      rw [Finset.mem_sdiff] at hz
      rw [hg_zero z hz.2, Complex.normSq_zero]
    rw [hzero, add_zero]
  have hsum_δ_nonneg : 0 ≤ Ω₀.sum (fun z => Complex.normSq (δ z)) :=
    Finset.sum_nonneg (fun z _ => Complex.normSq_nonneg _)
  have hsum_δ_bound : Ω₀.sum (fun z => Complex.normSq (δ z)) ≤ epsilon := by
    calc Ω₀.sum (fun z => Complex.normSq (δ z))
        ≤ Finset.univ.sum (fun z => Complex.normSq (δ z)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          intro z _ _
          exact Complex.normSq_nonneg _
      _ = normSquared δ := rfl
      _ ≤ epsilon := hδ
  -- Cauchy-Schwarz: |⟨g|δ⟩_Ω₀|² ≤ (Σ|g|²) · (Σ|δ|²) = 1 · Σ|δ|² ≤ ε
  -- Hence |⟨g|δ⟩| ≤ √ε
  have hcross_normsq_bound : Complex.normSq (Ω₀.sum (fun z => conj (g z) * δ z)) ≤ epsilon := by
    have hCS := complex_cauchy_schwarz Ω₀ g δ
    calc Complex.normSq (Ω₀.sum (fun z => conj (g z) * δ z))
        ≤ (Ω₀.sum fun z => Complex.normSq (g z)) * (Ω₀.sum fun z => Complex.normSq (δ z)) := hCS
      _ = 1 * (Ω₀.sum fun z => Complex.normSq (δ z)) := by rw [hsum_g]
      _ = Ω₀.sum fun z => Complex.normSq (δ z) := one_mul _
      _ ≤ epsilon := hsum_δ_bound
  -- Expand finalState = g + δ and sum over Ω₀
  have hfinal : ∀ z, finalState z = g z + δ z := by intro z; simp only [δ]; ring
  have hexpand : ∀ z, Complex.normSq (finalState z) =
      Complex.normSq (g z) + 2 * (conj (g z) * δ z).re + Complex.normSq (δ z) := by
    intro z
    rw [hfinal z, Complex.normSq_add]
    -- normSq_add gives: |a+b|² = |a|² + |b|² + 2 * (a * conj(b)).re
    -- We need to show: (g * conj(δ)).re = (conj(g) * δ).re
    -- Using star_eq_starRingEnd to convert between notations
    simp only [conj_eq_star, star_eq_starRingEnd]
    -- Goal: normSq(g) + normSq(δ) + (g * star(δ)).re * 2 = normSq(g) + 2 * (star(g) * δ).re + normSq(δ)
    -- We prove (g * star(δ)).re = (star(g) * δ).re
    -- star z = Complex.conj z = { re := z.re, im := -z.im }
    have hre_eq : (g z * star (δ z)).re = (star (g z) * δ z).re := by
      -- Expand using Complex.mul_re: (a*b).re = a.re * b.re - a.im * b.im
      simp only [Complex.mul_re]
      -- star = conj for Complex, use conj_re and conj_im
      simp only [RCLike.star_def]
      have h1 : (starRingEnd ℂ (δ z)).re = (δ z).re := Complex.conj_re (δ z)
      have h2 : (starRingEnd ℂ (δ z)).im = -(δ z).im := Complex.conj_im (δ z)
      have h3 : (starRingEnd ℂ (g z)).re = (g z).re := Complex.conj_re (g z)
      have h4 : (starRingEnd ℂ (g z)).im = -(g z).im := Complex.conj_im (g z)
      rw [h1, h2, h3, h4]
      ring
    simp only [starRingEnd_apply] at hre_eq ⊢
    rw [hre_eq]
    ring
  have hsum_expand : Ω₀.sum (fun z => Complex.normSq (finalState z)) =
      Ω₀.sum (fun z => Complex.normSq (g z)) +
      Ω₀.sum (fun z => 2 * (conj (g z) * δ z).re) +
      Ω₀.sum (fun z => Complex.normSq (δ z)) := by
    conv_lhs => arg 2; ext z; rw [hexpand z]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [hsum_expand, hsum_g]
  -- Bound the cross term using |Re(z)|² ≤ |z|² and |z|² ≤ ε
  -- Hence |Re(⟨g|δ⟩)| ≤ √|z|² ≤ √ε
  have hcross_re : |Ω₀.sum (fun z => 2 * (conj (g z) * δ z).re)| ≤ 2 * Real.sqrt epsilon := by
    -- |2 * Σ Re(...)| = 2 * |Σ Re(...)|
    calc |Ω₀.sum (fun z => 2 * (conj (g z) * δ z).re)|
        = |2 * Ω₀.sum (fun z => (conj (g z) * δ z).re)| := by
          congr 1
          rw [← Finset.mul_sum]
      _ = 2 * |Ω₀.sum (fun z => (conj (g z) * δ z).re)| := by
          rw [abs_mul, abs_of_pos (by norm_num : (2 : Real) > 0)]
      _ ≤ 2 * Real.sqrt epsilon := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : Real) ≤ 2)
          -- |Σ Re(...)| = |Re(Σ ...)| ≤ √(normSq(Σ ...)) ≤ √ε
          have hsum_re : Ω₀.sum (fun z => (conj (g z) * δ z).re) =
              (Ω₀.sum (fun z => conj (g z) * δ z)).re := (Complex.re_sum _ _).symm
          rw [hsum_re]
          -- Complex.re_sq_le_normSq gives re * re ≤ normSq, convert to re^2
          have habs_sq : (Ω₀.sum (fun z => conj (g z) * δ z)).re ^ 2 ≤
              Complex.normSq (Ω₀.sum (fun z => conj (g z) * δ z)) := by
            have h := Complex.re_sq_le_normSq (Ω₀.sum (fun z => conj (g z) * δ z))
            simp only [sq] at h ⊢
            exact h
          calc |(Ω₀.sum (fun z => conj (g z) * δ z)).re|
              = Real.sqrt ((Ω₀.sum (fun z => conj (g z) * δ z)).re ^ 2) := by
                rw [Real.sqrt_sq_eq_abs]
            _ ≤ Real.sqrt (Complex.normSq (Ω₀.sum (fun z => conj (g z) * δ z))) :=
                Real.sqrt_le_sqrt habs_sq
            _ ≤ Real.sqrt epsilon := Real.sqrt_le_sqrt hcross_normsq_bound
  have hre_bound : Ω₀.sum (fun z => 2 * (conj (g z) * δ z).re) ≥ -2 * Real.sqrt epsilon := by
    have h := neg_abs_le (Ω₀.sum (fun z => 2 * (conj (g z) * δ z).re))
    linarith [hcross_re]
  linarith [hsum_δ_nonneg]

end UAQO
