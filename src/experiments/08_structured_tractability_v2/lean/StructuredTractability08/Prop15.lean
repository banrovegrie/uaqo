import Mathlib

namespace StructuredTractability08

/-- c_B parameter in Proposition 15. -/
def cB (B : ℚ) : ℚ := (7 * B) / (B^2 + 6)

/--
Exact A1 matching identity in Proposition 15:
(1/8)(B + 3/B) = (1/16)(B + 7/c_B).
-/
theorem prop15_a1_match (B : ℚ) (hB : B ≠ 0) :
    (1 / 8 : ℚ) * (B + 3 / B)
      = (1 / 16 : ℚ) * (B + 7 / cB B) := by
  unfold cB
  field_simp [hB]
  ring

/--
For B > 1, the Prop 15 parameter c_B lies strictly between 1/B and B.
-/
theorem cB_between (B : ℚ) (hB : 1 < B) :
    1 / B < cB B ∧ cB B < B := by
  have hB0 : B ≠ 0 := by linarith
  have hden0 : B ^ 2 + 6 ≠ 0 := by nlinarith [hB]
  constructor
  · unfold cB
    field_simp [hB0, hden0]
    nlinarith [hB]
  · unfold cB
    field_simp [hden0]
    nlinarith [hB]

/--
Quantitative constant used in the Proposition 15 partition-gap lower bound:
`exp(-21/5) < 3/200`.
-/
lemma exp_neg_21_div5_lt_three_div_200 : Real.exp (-(21 : ℝ) / 5) < (3 : ℝ) / 200 := by
  have hexp : ((200 : ℝ) / 3) < Real.exp ((21 : ℝ) / 5) := by
    have hsum : Finset.sum (Finset.range 14)
        (fun k : ℕ => (((21 : ℝ) / 5) ^ k) / (Nat.factorial k))
        ≤ Real.exp ((21 : ℝ) / 5) := by
      simpa using (Real.sum_le_exp_of_nonneg (x := (21 : ℝ) / 5) (by positivity) 14)
    have hval : ((200 : ℝ) / 3) < Finset.sum (Finset.range 14)
        (fun k : ℕ => (((21 : ℝ) / 5) ^ k) / (Nat.factorial k)) := by
      norm_num
    exact lt_of_lt_of_le hval hsum
  have hdiv : 1 / Real.exp ((21 : ℝ) / 5) < 1 / (((200 : ℝ) / 3)) :=
    one_div_lt_one_div_of_lt (show 0 < (200 : ℝ) / 3 by positivity) hexp
  have htarget : (1 : ℝ) / (((200 : ℝ) / 3)) = (3 : ℝ) / 200 := by norm_num
  have hneg : (-(21 : ℝ) / 5) = -((21 : ℝ) / 5) := by ring
  simpa [hneg, Real.exp_neg, htarget, one_div] using hdiv

/--
Auxiliary lower bound used in the Proposition 15 partition-gap estimate:
`1/3 < exp(-1)`.
-/
lemma exp_neg_one_gt_one_div_three : (1 : ℝ) / 3 < Real.exp (-1) := by
  have h3 : Real.exp (1 : ℝ) < 3 := Real.exp_one_lt_three
  have hdiv : (1 : ℝ) / 3 < 1 / Real.exp (1 : ℝ) := by
    simpa [one_div] using (one_div_lt_one_div_of_lt (Real.exp_pos (1 : ℝ)) h3)
  simpa [Real.exp_neg, one_div] using hdiv

/--
Monotone lower bound on the Prop 15 exponent ratio for `B >= 3`:
`21/5 <= 7 B^2 / (B^2 + 6)`.
-/
lemma ratio_ge_21_div_5 (B : ℝ) (hB : 3 ≤ B) :
    (21 : ℝ) / 5 ≤ (7 * B ^ 2) / (B ^ 2 + 6) := by
  have hden : 0 < B ^ 2 + 6 := by positivity
  have hmul : (21 : ℝ) / 5 * (B ^ 2 + 6) ≤ 7 * B ^ 2 := by
    nlinarith [hB]
  exact (le_div_iff₀ hden).2 hmul

/--
The exponential part in Proposition 15 is uniformly small for `B >= 3`.
-/
lemma exp_neg_ratio_le_exp_neg_21_div_5 (B : ℝ) (hB : 3 ≤ B) :
    Real.exp (-(7 * B ^ 2 / (B ^ 2 + 6))) ≤ Real.exp (-(21 : ℝ) / 5) := by
  have hratio : (21 : ℝ) / 5 ≤ (7 * B ^ 2) / (B ^ 2 + 6) := ratio_ge_21_div_5 B hB
  have hneg : -(7 * B ^ 2 / (B ^ 2 + 6)) ≤ -21 / 5 := by linarith
  exact (Real.exp_le_exp).2 hneg

/--
Machine-checked core inequality behind Proposition 15's partition-gap claim:
for all `B >= 3`,
`exp(-1)/16 - (7/16) * exp(-7 B^2/(B^2+6)) > 1/100`.
-/
theorem prop15_gap_core_bound (B : ℝ) (hB : 3 ≤ B) :
    (Real.exp (-1)) / 16 - (7 / 16 : ℝ) * Real.exp (-(7 * B ^ 2 / (B ^ 2 + 6))) > 1 / 100 := by
  have h1 : (Real.exp (-1)) / 16 > ((1 : ℝ) / 3) / 16 := by
    have h := exp_neg_one_gt_one_div_three
    nlinarith
  have h2 : Real.exp (-(7 * B ^ 2 / (B ^ 2 + 6))) < (3 : ℝ) / 200 := by
    have hle := exp_neg_ratio_le_exp_neg_21_div_5 B hB
    have hlt := exp_neg_21_div5_lt_three_div_200
    exact lt_of_le_of_lt hle hlt
  have h3 : (7 / 16 : ℝ) * Real.exp (-(7 * B ^ 2 / (B ^ 2 + 6))) < (7 / 16 : ℝ) * ((3 : ℝ) / 200) := by
    exact mul_lt_mul_of_pos_left h2 (by positivity)
  have h4 : (Real.exp (-1)) / 16 - (7 / 16 : ℝ) * Real.exp (-(7 * B ^ 2 / (B ^ 2 + 6)))
      > ((1 : ℝ) / 3) / 16 - (7 / 16 : ℝ) * ((3 : ℝ) / 200) := by
    linarith
  have h5 : ((1 : ℝ) / 3) / 16 - (7 / 16 : ℝ) * ((3 : ℝ) / 200) > 1 / 100 := by
    norm_num
  exact lt_trans h5 h4

end StructuredTractability08
