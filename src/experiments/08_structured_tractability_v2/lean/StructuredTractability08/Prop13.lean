import Mathlib

open scoped BigOperators

namespace StructuredTractability08

/--
Generic tail suppression bound used in Proposition 13.
If all excited energies in a finite set satisfy `E(i) >= Δ`, then
`sum exp(-B E(i)) (B + 1/E(i))` is bounded by cardinality times the worst-case
value at `Δ`.
-/
theorem tail_sum_bound {α : Type} (s : Finset α) (E : α → ℝ) (B Δ : ℝ)
    (hB : 0 ≤ B) (hΔ : 0 < Δ)
    (hE : ∀ i ∈ s, Δ ≤ E i) :
    (∑ i ∈ s, Real.exp (-B * E i) * (B + 1 / E i))
      ≤ (s.card : ℝ) * (Real.exp (-B * Δ) * (B + 1 / Δ)) := by
  have hterm : ∀ i ∈ s,
      Real.exp (-B * E i) * (B + 1 / E i)
        ≤ Real.exp (-B * Δ) * (B + 1 / Δ) := by
    intro i hi
    have hEi : Δ ≤ E i := hE i hi
    have hEi_pos : 0 < E i := lt_of_lt_of_le hΔ hEi
    have hExp : Real.exp (-B * E i) ≤ Real.exp (-B * Δ) := by
      have hmul : B * Δ ≤ B * E i := mul_le_mul_of_nonneg_left hEi hB
      have hneg : -B * E i ≤ -B * Δ := by nlinarith [hmul]
      exact (Real.exp_le_exp).2 hneg
    have hInv : 1 / E i ≤ 1 / Δ := by
      simpa [one_div] using (one_div_le_one_div_of_le hΔ hEi)
    have hAdd : B + 1 / E i ≤ B + 1 / Δ := by
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hInv B
    have hAdd_nonneg_i : 0 ≤ B + 1 / E i := by
      have hInv_nonneg : 0 ≤ 1 / E i := one_div_nonneg.mpr (le_of_lt hEi_pos)
      linarith [hB, hInv_nonneg]
    have hExp_nonneg : 0 ≤ Real.exp (-B * Δ) := by positivity
    exact mul_le_mul hExp hAdd hAdd_nonneg_i hExp_nonneg
  have hsum :
      (∑ i ∈ s, Real.exp (-B * E i) * (B + 1 / E i))
      ≤ ∑ i ∈ s, (Real.exp (-B * Δ) * (B + 1 / Δ)) := by
    exact Finset.sum_le_sum hterm
  simpa using (le_trans hsum (by simp))

/--
Three-term absolute-value decomposition used in Proposition 13:
`|a-d| <= |a-b| + |b-c| + |c-d|`.
-/
theorem three_term_abs_bound (a b c d : ℝ) :
    |a - d| ≤ |a - b| + |b - c| + |c - d| := by
  have h1 : |a - d| ≤ |a - b| + |b - d| := abs_sub_le a b d
  have h2 : |b - d| ≤ |b - c| + |c - d| := abs_sub_le b c d
  nlinarith

/--
Oracle-sampling contribution in Proposition 13:
if each queried difference is bounded by `2*μ*N`, then the midpoint average is
bounded by `2*μ*B`.
-/
theorem oracle_midpoint_bound (K : ℕ) (B μ N : ℝ)
    (hK : 0 < K) (hB : 0 ≤ B) (hN : 0 < N)
    (err : ℕ → ℝ)
    (herr : ∀ i ∈ Finset.range K, |err i| ≤ 2 * μ * N) :
    |(B / ((K : ℝ) * N)) * (∑ i ∈ Finset.range K, err i)| ≤ 2 * μ * B := by
  have hcoeff_nonneg : 0 ≤ B / ((K : ℝ) * N) := by positivity
  have hsum_abs : |∑ i ∈ Finset.range K, err i| ≤ ∑ i ∈ Finset.range K, |err i| := by
    exact Finset.abs_sum_le_sum_abs err (Finset.range K)
  have hsum_bound : ∑ i ∈ Finset.range K, |err i| ≤ ∑ i ∈ Finset.range K, (2 * μ * N) := by
    exact Finset.sum_le_sum (fun i hi => herr i hi)
  have hsum_bound' : |∑ i ∈ Finset.range K, err i| ≤ ∑ i ∈ Finset.range K, (2 * μ * N) := by
    exact le_trans hsum_abs hsum_bound
  have hmul_bound :
      |(B / ((K : ℝ) * N)) * (∑ i ∈ Finset.range K, err i)|
      ≤ (B / ((K : ℝ) * N)) * (∑ i ∈ Finset.range K, (2 * μ * N)) := by
    calc
      |(B / ((K : ℝ) * N)) * (∑ i ∈ Finset.range K, err i)|
          = |B / ((K : ℝ) * N)| * |∑ i ∈ Finset.range K, err i| := by
            simp [abs_mul]
      _ = (B / ((K : ℝ) * N)) * |∑ i ∈ Finset.range K, err i| := by
            simp [abs_of_nonneg hcoeff_nonneg]
      _ ≤ (B / ((K : ℝ) * N)) * (∑ i ∈ Finset.range K, (2 * μ * N)) := by
            gcongr
  have hsum_const : (∑ i ∈ Finset.range K, (2 * μ * N)) = (K : ℝ) * (2 * μ * N) := by
    simp
  calc
    |(B / ((K : ℝ) * N)) * (∑ i ∈ Finset.range K, err i)|
      ≤ (B / ((K : ℝ) * N)) * (∑ i ∈ Finset.range K, (2 * μ * N)) := hmul_bound
    _ = (B / ((K : ℝ) * N)) * ((K : ℝ) * (2 * μ * N)) := by rw [hsum_const]
    _ = 2 * μ * B := by
      have hKne : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
      field_simp [hN.ne', hKne]

/--
Quadrature aggregation algebra used in Proposition 13:
if each interval contributes at most `L * (B/K)^2 / 2` in absolute error, then the
total over `K` intervals is at most `L * B^2 / (2K)`.
-/
theorem midpoint_interval_aggregation_bound (K : ℕ) (B L : ℝ)
    (hK : 0 < K)
    (err : ℕ → ℝ)
    (herr : ∀ i ∈ Finset.range K, |err i| ≤ L * (B / (K : ℝ)) ^ 2 / 2) :
    |∑ i ∈ Finset.range K, err i| ≤ L * B ^ 2 / (2 * (K : ℝ)) := by
  have hsum_abs : |∑ i ∈ Finset.range K, err i| ≤ ∑ i ∈ Finset.range K, |err i| := by
    exact Finset.abs_sum_le_sum_abs err (Finset.range K)
  have hsum_bound :
      ∑ i ∈ Finset.range K, |err i| ≤ ∑ i ∈ Finset.range K, (L * (B / (K : ℝ)) ^ 2 / 2) := by
    exact Finset.sum_le_sum (fun i hi => herr i hi)
  have hpre :
      |∑ i ∈ Finset.range K, err i|
      ≤ ∑ i ∈ Finset.range K, (L * (B / (K : ℝ)) ^ 2 / 2) := by
    exact le_trans hsum_abs hsum_bound
  have hsum_const :
      (∑ i ∈ Finset.range K, (L * (B / (K : ℝ)) ^ 2 / 2))
      = (K : ℝ) * (L * (B / (K : ℝ)) ^ 2 / 2) := by
    simp
  have hKne : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hsimpl : (K : ℝ) * (L * (B / (K : ℝ)) ^ 2 / 2) = L * B ^ 2 / (2 * (K : ℝ)) := by
    field_simp [hKne]
  exact le_trans hpre (by simp [hsum_const, hsimpl])

/--
Parameter-choice check in Proposition 13:
if each of the three terms is at most `η/3`, the total error budget is at most `η`.
-/
theorem prop13_eta_budget (tail μ B R K η : ℝ)
    (hη : 0 < η) (hB : 0 < B) (hK : 0 < K)
    (htail : tail ≤ η / 3)
    (hμ : μ ≤ η / (6 * B))
    (hKchoice : (3 * R * B ^ 2) / (2 * η) ≤ K) :
    tail + 2 * μ * B + (R * B ^ 2) / (2 * K) ≤ η := by
  have h_oracle : 2 * μ * B ≤ η / 3 := by
    have hmul : 2 * μ * B ≤ 2 * (η / (6 * B)) * B := by
      gcongr
    have hsimpl : 2 * (η / (6 * B)) * B = η / 3 := by
      have hBne : B ≠ 0 := ne_of_gt hB
      field_simp [hBne]
      norm_num
    nlinarith [hmul, hsimpl]
  have hquadmul : 3 * (R * B ^ 2) ≤ 2 * η * K := by
    have hη2 : 0 ≤ 2 * η := by positivity
    have hscaled : (2 * η) * ((3 * R * B ^ 2) / (2 * η)) ≤ (2 * η) * K :=
      mul_le_mul_of_nonneg_left hKchoice hη2
    have hsimpl : (2 * η) * ((3 * R * B ^ 2) / (2 * η)) = 3 * (R * B ^ 2) := by
      have hηne : η ≠ 0 := ne_of_gt hη
      field_simp [hηne]
    nlinarith [hscaled, hsimpl]
  have h_quad : (R * B ^ 2) / (2 * K) ≤ η / 3 := by
    have htmp : R * B ^ 2 ≤ (η / 3) * (2 * K) := by nlinarith [hquadmul]
    have hK2 : 0 < 2 * K := by positivity
    exact (div_le_iff₀ hK2).2 htmp
  nlinarith [htail, h_oracle, h_quad]

end StructuredTractability08
