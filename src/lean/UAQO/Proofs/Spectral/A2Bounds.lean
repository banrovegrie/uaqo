/-
  Proofs for A2 lower bound axiom in SpectralParameters.lean.

  Eliminates:
  - A2_lower_bound
-/
import UAQO.Spectral.SpectralParameters

namespace UAQO.Proofs.Spectral

open UAQO

/-- A₂ ≥ (1 - d₀/N) / Δ²

    Proof: A₂ = (1/N) Σ_{k≥1} d_k / (E_k - E₀)²

    Since E_k - E₀ ≥ Δ for all k ≥ 1 (by definition of spectral gap),
    we have 1/(E_k - E₀)² ≥ 1/Δ² for each term.

    Therefore:
    A₂ ≥ (1/N) Σ_{k≥1} d_k / Δ²
       = (1/(N Δ²)) Σ_{k≥1} d_k
       = (N - d₀) / (N Δ²)
       = (1 - d₀/N) / Δ²
-/
theorem A2_lower_bound_proof {n M : Nat} (es : EigenStructure n M) (hM : M >= 2) :
    A2 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM) >=
    (1 - (es.degeneracies ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩ : Real) / qubitDim n) /
    (spectralGapDiag es hM)^2 := by
  simp only [A2, spectralParam, spectralGapDiag]
  have hM0 : M > 0 := Nat.lt_of_lt_of_le Nat.zero_lt_two hM
  have hN : (qubitDim n : Real) > 0 := Nat.cast_pos.mpr (Nat.pow_pos (by norm_num : 0 < 2))
  have hE0 : es.eigenvalues ⟨0, hM0⟩ = 0 := es.ground_energy_zero hM0
  have hDelta : es.eigenvalues ⟨1, hM⟩ - es.eigenvalues ⟨0, hM0⟩ > 0 := by
    have h := es.eigenval_ordered ⟨0, hM0⟩ ⟨1, hM⟩
    simp only [Fin.mk_lt_mk] at h
    linarith [h Nat.zero_lt_one]
  have hDelta' : es.eigenvalues ⟨1, hM⟩ > 0 := by rw [hE0] at hDelta; linarith

  -- Key: for k ≥ 1, E_k - E₀ ≥ Δ = E₁ - E₀
  have hgap_bound : ∀ k : Fin M, k.val > 0 →
      es.eigenvalues k - es.eigenvalues ⟨0, hM0⟩ >= es.eigenvalues ⟨1, hM⟩ - es.eigenvalues ⟨0, hM0⟩ := by
    intro k hk
    by_cases h1 : k.val = 1
    · simp only [h1, le_refl]
    · have hk_ge : k.val >= 1 := hk
      have hk_ne : k.val ≠ 1 := h1
      have hk_gt : k.val > 1 := Nat.lt_of_le_of_ne hk_ge (Ne.symm hk_ne)
      have hord := es.eigenval_ordered ⟨1, hM⟩ k hk_gt
      linarith

  -- Each term d_k/(E_k - E₀)² ≥ d_k/Δ²
  have hterm_bound : ∀ k ∈ Finset.filter (fun k : Fin M => k.val > 0) Finset.univ,
      (es.degeneracies k : Real) / (es.eigenvalues k - es.eigenvalues ⟨0, hM0⟩)^2 >=
      (es.degeneracies k : Real) / (es.eigenvalues ⟨1, hM⟩ - es.eigenvalues ⟨0, hM0⟩)^2 := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    have hgap := hgap_bound k hk
    have hdk : (es.degeneracies k : Real) >= 0 := Nat.cast_nonneg _
    apply div_le_div_of_nonneg_left hdk
    · apply sq_pos_of_pos hDelta
    · apply sq_le_sq' (by linarith) hgap

  -- Sum the bounds
  have hsum_bound : Finset.sum (Finset.filter (fun k : Fin M => k.val > 0) Finset.univ)
      (fun k => (es.degeneracies k : Real) / (es.eigenvalues k - es.eigenvalues ⟨0, hM0⟩)^2) >=
      Finset.sum (Finset.filter (fun k : Fin M => k.val > 0) Finset.univ)
      (fun k => (es.degeneracies k : Real) / (es.eigenvalues ⟨1, hM⟩ - es.eigenvalues ⟨0, hM0⟩)^2) := by
    apply Finset.sum_le_sum hterm_bound

  -- Factor out the common denominator
  have hfactor : Finset.sum (Finset.filter (fun k : Fin M => k.val > 0) Finset.univ)
      (fun k => (es.degeneracies k : Real) / (es.eigenvalues ⟨1, hM⟩ - es.eigenvalues ⟨0, hM0⟩)^2) =
      (Finset.sum (Finset.filter (fun k : Fin M => k.val > 0) Finset.univ)
        (fun k => (es.degeneracies k : Real))) / (es.eigenvalues ⟨1, hM⟩ - es.eigenvalues ⟨0, hM0⟩)^2 := by
    rw [Finset.sum_div]

  -- The sum of d_k for k > 0 equals N - d₀
  have hsum_deg : Finset.sum (Finset.filter (fun k : Fin M => k.val > 0) Finset.univ)
      (fun k => (es.degeneracies k : Real)) =
      (qubitDim n : Real) - (es.degeneracies ⟨0, hM0⟩ : Real) := by
    have htotal := es.deg_sum
    -- Σ_k d_k = N, so Σ_{k>0} d_k = N - d_0
    have hsplit : Finset.sum Finset.univ (fun k : Fin M => (es.degeneracies k : Real)) =
        (es.degeneracies ⟨0, hM0⟩ : Real) +
        Finset.sum (Finset.filter (fun k : Fin M => k.val > 0) Finset.univ)
          (fun k => (es.degeneracies k : Real)) := by
      rw [← Finset.insert_erase (Finset.mem_univ ⟨0, hM0⟩)]
      rw [Finset.sum_insert (Finset.not_mem_erase _ _)]
      congr 1
      apply Finset.sum_congr
      · ext k
        simp only [Finset.mem_erase, Finset.mem_univ, true_and, Finset.mem_filter, ne_eq]
        constructor
        · intro ⟨hne, _⟩
          exact Nat.pos_of_ne_zero (Fin.val_ne_of_ne hne)
        · intro hpos
          exact ⟨Fin.ne_of_val_ne (Nat.ne_of_gt hpos), trivial⟩
      · intro _ _; rfl
    have htotal_real : (qubitDim n : Real) = Finset.sum Finset.univ (fun k : Fin M => (es.degeneracies k : Real)) := by
      rw [← htotal]
      simp only [Nat.cast_sum]
    rw [htotal_real, hsplit]
    ring

  -- Combine everything
  calc (1 / qubitDim n) * Finset.sum (Finset.filter (fun k => k.val > 0) Finset.univ)
         (fun k => (es.degeneracies k : Real) / (es.eigenvalues k - es.eigenvalues ⟨0, hM0⟩)^2)
      >= (1 / qubitDim n) * Finset.sum (Finset.filter (fun k => k.val > 0) Finset.univ)
         (fun k => (es.degeneracies k : Real) / (es.eigenvalues ⟨1, hM⟩ - es.eigenvalues ⟨0, hM0⟩)^2) := by
        apply mul_le_mul_of_nonneg_left hsum_bound (div_nonneg one_pos.le (le_of_lt hN))
    _ = (1 / qubitDim n) * ((qubitDim n - es.degeneracies ⟨0, hM0⟩) /
          (es.eigenvalues ⟨1, hM⟩ - es.eigenvalues ⟨0, hM0⟩)^2) := by
        rw [hfactor, hsum_deg]
    _ = (1 - (es.degeneracies ⟨0, hM0⟩ : Real) / qubitDim n) /
          (es.eigenvalues ⟨1, hM⟩ - es.eigenvalues ⟨0, hM0⟩)^2 := by
        field_simp
        ring

end UAQO.Proofs.Spectral
