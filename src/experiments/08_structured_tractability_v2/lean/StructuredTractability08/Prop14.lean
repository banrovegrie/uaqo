import Mathlib

namespace StructuredTractability08

/--
Algebraic identity used in Proposition 14:
  s*(A+e) - s*(A) = e / ((1+A)(1+A+e)), where s*(x) = x/(1+x).
-/
theorem crossing_shift_identity (A e : ℚ)
    (h1 : 1 + A ≠ 0) (h2 : 1 + A + e ≠ 0) :
    (A + e) / (1 + A + e) - A / (1 + A)
      = e / ((1 + A) * (1 + A + e)) := by
  field_simp [h1, h2]
  ring

/--
Absolute-value sensitivity bound used in Proposition 14.
This is the local regime bound under |e| <= (1+A)/2.
-/
theorem crossing_shift_abs_bound (A e : ℚ)
    (hA : 0 < 1 + A) (he : |e| ≤ (1 + A) / 2) :
    |(A + e) / (1 + A + e) - A / (1 + A)|
      ≤ 2 * |e| / (1 + A) ^ 2 := by
  have h1 : 1 + A ≠ 0 := by linarith
  have h2half : (1 + A) / 2 ≤ 1 + A + e := by
    have heLow : -((1 + A) / 2) ≤ e := (abs_le.mp he).1
    linarith
  have h2pos : 0 < 1 + A + e := by
    have : 0 < (1 + A) / 2 := by linarith
    linarith
  have h2 : 1 + A + e ≠ 0 := by linarith
  have hid := crossing_shift_identity A e h1 h2
  rw [hid]
  have hden_nonneg : 0 ≤ (1 + A) * (1 + A + e) := by nlinarith [hA, h2pos]
  have hden_pos : 0 < (1 + A) * (1 + A + e) := by nlinarith [hA, h2pos]
  rw [abs_div, abs_of_nonneg hden_nonneg]
  have hden_lower : (1 + A) ^ 2 / 2 ≤ (1 + A) * (1 + A + e) := by
    have hmul :=
      mul_le_mul_of_nonneg_left h2half (show 0 ≤ 1 + A by linarith)
    have hleft : (1 + A) * ((1 + A) / 2) = (1 + A) ^ 2 / 2 := by ring
    calc
      (1 + A) ^ 2 / 2 = (1 + A) * ((1 + A) / 2) := by simp [hleft]
      _ ≤ (1 + A) * (1 + A + e) := hmul
  have hrecip :
      1 / ((1 + A) * (1 + A + e)) ≤ 1 / ((1 + A) ^ 2 / 2) := by
    exact one_div_le_one_div_of_le (show 0 < (1 + A) ^ 2 / 2 by positivity) hden_lower
  have hsq_pos : 0 < (1 + A) ^ 2 := by nlinarith [hA]
  have hsq_ne : (1 + A) ^ 2 ≠ 0 := ne_of_gt hsq_pos
  have hrecip' : 1 / ((1 + A) ^ 2 / 2) = 2 / (1 + A) ^ 2 := by
    field_simp [hsq_ne]
  have hbound_inv : 1 / ((1 + A) * (1 + A + e)) ≤ 2 / (1 + A) ^ 2 := by
    simpa [hrecip'] using hrecip
  have hmul_bound : |e| * (1 / ((1 + A) * (1 + A + e)))
      ≤ |e| * (2 / (1 + A) ^ 2) := by
    exact mul_le_mul_of_nonneg_left hbound_inv (abs_nonneg e)
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul_bound

/--
If |e| is at most the local regime threshold and also at most the scaled target
delta, then the crossing shift is bounded by that target delta.
-/
theorem crossing_shift_target_bound (A e ds : ℚ)
    (hA : 0 < 1 + A)
    (he :
      |e| ≤ min ((1 + A) / 2) (((1 + A) ^ 2 / 2) * ds)) :
    |(A + e) / (1 + A + e) - A / (1 + A)| ≤ ds := by
  have heLocal : |e| ≤ (1 + A) / 2 := le_trans he (min_le_left _ _)
  have heTarget : |e| ≤ ((1 + A) ^ 2 / 2) * ds := le_trans he (min_le_right _ _)
  have hbase := crossing_shift_abs_bound A e hA heLocal
  have hAposSq : 0 < (1 + A) ^ 2 := by nlinarith [hA]
  have hbound_div : 2 * |e| / (1 + A) ^ 2 ≤ ds := by
    refine (div_le_iff₀ hAposSq).2 ?_
    have hmul0 : 2 * |e| ≤ (1 + A) ^ 2 * ds := by
      nlinarith [heTarget]
    have hmul : 2 * |e| ≤ ds * (1 + A) ^ 2 := by
      nlinarith [hmul0]
    exact hmul
  exact le_trans hbase hbound_div

/--
Pure algebraic scale identity used when substituting the paper's delta_s formula.
-/
theorem scale_substitution_identity (u x : ℚ) (hu : u ≠ 0) :
    (u ^ 2 / 2) * ((2 / (u ^ 2)) * x) = x := by
  field_simp [hu]

end StructuredTractability08
