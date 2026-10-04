import CurveComplexGenusTwo.Hyperbolic.CompactCircleStripArea
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactTriangleAngleIntegralCandidate

namespace CurveComplex.Hyperbolic
open Set MeasureTheory
open scoped MeasureTheory NNReal ENNReal

set_option maxHeartbeats 2000000 in
theorem compact_canonical_radial_triangle_strip_area :
    let t := Real.sqrt 3 + Real.sqrt 2
    let a := -(Real.sqrt 3 + 2 * Real.sqrt 2) / 5
    (μHE[2] : Measure H2)
      {z | a < z.re ∧ z.re < 0 ∧
        Real.sqrt (4 - (z.re + Real.sqrt 3) ^ 2) < z.im ∧
        z.im < Real.sqrt (2 * t ^ 2 - (z.re - t) ^ 2)} =
      ENNReal.ofReal (Real.pi / 12) := by
  dsimp only
  let t := Real.sqrt 3 + Real.sqrt 2
  let a := -(Real.sqrt 3 + 2 * Real.sqrt 2) / 5
  have hs₃ : (Real.sqrt 3) ^ 2 = 3 := by norm_num
  have hs₂ : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hp₃ : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hp₂ : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h₂lo : 7 / 5 < Real.sqrt 2 := by nlinarith [hs₂]
  have h₂hi : Real.sqrt 2 < 3 / 2 := by nlinarith [hs₂]
  have h₃lo : 8 / 5 < Real.sqrt 3 := by nlinarith [hs₃]
  have h₃hi : Real.sqrt 3 < 7 / 4 := by nlinarith [hs₃]
  have ht : 0 < t := by dsimp [t]; positivity
  have ht₃ : 3 < t := by dsimp [t]; linarith
  have ha : a < 0 := by dsimp [a]; linarith
  have ha₁ : -1 < a := by dsimp [a]; linarith
  have hleft₀ : -Real.sqrt 3 - 2 < a := by dsimp [a]; linarith
  have hright₀ : (0 : ℝ) < -Real.sqrt 3 + 2 := by linarith
  have hleft₁ : t - Real.sqrt 2 * t < a := by
    have hm : 0 < (Real.sqrt 2 - 7 / 5) * t := mul_pos (by linarith) ht
    nlinarith [hm]
  have hright₁ : (0 : ℝ) < t + Real.sqrt 2 * t := by positivity
  have hmeet : t ^ 2 - 1 + 2 * (t + Real.sqrt 3) * a = 0 := by
    dsimp [t, a]
    nlinarith [hs₃, hs₂]
  have horder : ∀ x ∈ Ioo a 0,
      Real.sqrt (2 ^ 2 - (x - -Real.sqrt 3) ^ 2) ≤
      Real.sqrt ((Real.sqrt 2 * t) ^ 2 - (x - t) ^ 2) := by
    intro x hx
    apply Real.sqrt_le_sqrt
    have hm : 0 < (t + Real.sqrt 3) * (x-a) := mul_pos (by positivity) (by linarith [hx.1])
    have hs : (Real.sqrt 2 * t) ^ 2 = 2 * t ^ 2 := by rw [mul_pow, hs₂]
    rw [hs]
    nlinarith [hm, hmeet, hs₃]
  have h := compact_circle_strip_normalized_area (-Real.sqrt 3) t 2 (Real.sqrt 2 * t) a 0
    (by norm_num) (by positivity) ha.le hleft₀ hright₀ hleft₁ hright₁ horder
  have hs : (Real.sqrt 2 * t) ^ 2 = 2 * t ^ 2 := by rw [mul_pow, hs₂]
  have hratio : (-t) / (Real.sqrt 2 * t) = -1 / Real.sqrt 2 := by
    field_simp <;> ring
  simp only [hs, hratio, zero_sub, sub_neg_eq_add, zero_add] at h
  have haVal := compact_right_triangle_arcsine_value
  change (Real.arcsin (Real.sqrt 3 / 2) - Real.arcsin ((a + Real.sqrt 3) / 2)) -
    (Real.arcsin (-1 / Real.sqrt 2) - Real.arcsin ((a-t) / (Real.sqrt 2 * t))) = Real.pi / 12 at haVal
  rw [haVal] at h
  simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using h

end CurveComplex.Hyperbolic
