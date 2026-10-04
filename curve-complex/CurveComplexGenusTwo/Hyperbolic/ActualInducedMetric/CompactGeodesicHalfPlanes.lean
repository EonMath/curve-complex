import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.VerticalReflectionCrossing
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactVertexGeodesics

namespace CurveComplex.Hyperbolic

theorem vertical_reflection_distance_le (a z : H2) (ha : 0 ≤ a.re) (hz : z.re ≤ 0) :
    dist a (verticalReflectionEquiv z) ≤ dist a z := by
  apply (Real.cosh_strictMonoOn.le_iff_le dist_nonneg dist_nonneg).mp
  rw [UpperHalfPlane.cosh_dist', UpperHalfPlane.cosh_dist',
    verticalReflection_re, verticalReflection_im]
  rw [div_le_div_iff_of_pos_right (show 0 < 2 * a.im * z.im by positivity)]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos ha hz]

theorem vertical_reflection_distance_lt (a z : H2) (ha : 0 < a.re) (hz : z.re < 0) :
    dist a (verticalReflectionEquiv z) < dist a z := by
  apply (Real.cosh_strictMonoOn.lt_iff_lt dist_nonneg dist_nonneg).mp
  rw [UpperHalfPlane.cosh_dist', UpperHalfPlane.cosh_dist',
    verticalReflection_re, verticalReflection_im]
  rw [div_lt_div_iff_of_pos_right (show 0 < 2 * a.im * z.im by positivity)]
  nlinarith [mul_neg_of_pos_of_neg ha hz]

theorem metric_segment_in_positive_vertical_halfplane (a b z : H2)
    (ha : 0 ≤ a.re) (hb : 0 ≤ b.re)
    (hz : dist a z + dist z b = dist a b) : 0 ≤ z.re := by
  by_contra h
  have hzr : z.re < 0 := lt_of_not_ge h
  have hla := vertical_reflection_distance_le a z ha hzr.le
  have hlb := vertical_reflection_distance_le b z hb hzr.le
  have ht := dist_triangle a (verticalReflectionEquiv z) b
  rw [dist_comm (verticalReflectionEquiv z) b] at ht
  rw [dist_comm z b] at hz
  by_cases hap : 0 < a.re
  · have hs := vertical_reflection_distance_lt a z hap hzr
    linarith
  by_cases hbp : 0 < b.re
  · have hs := vertical_reflection_distance_lt b z hbp hzr
    linarith
  have har : a.re = 0 := le_antisymm (le_of_not_gt hap) ha
  have hbr : b.re = 0 := le_antisymm (le_of_not_gt hbp) hb
  have hseg : dist a z + dist z b = dist a b := by simpa only [dist_comm] using hz
  have hr := metric_segment_on_vertical (har.trans hbr.symm) hseg
  rw [har] at hr
  linarith

theorem metric_segment_in_negative_vertical_halfplane (a b z : H2)
    (ha : a.re ≤ 0) (hb : b.re ≤ 0)
    (hz : dist a z + dist z b = dist a b) : z.re ≤ 0 := by
  have hr := metric_segment_in_positive_vertical_halfplane
    (verticalReflectionEquiv a) (verticalReflectionEquiv b) (verticalReflectionEquiv z)
    (by simpa only [verticalReflection_re, neg_nonneg] using ha)
    (by simpa only [verticalReflection_re, neg_nonneg] using hb)
    (by simpa only [verticalReflectionEquiv.dist_eq] using hz)
  simpa only [verticalReflection_re, neg_nonneg] using hr

theorem unit_circleStraightener_real_formula (z : H2) :
    (circleStraightener 0 1 z).re = (1 - z.re ^ 2 - z.im ^ 2) /
      (2 * ((z.re - 1) ^ 2 + z.im ^ 2)) := by
  change (circleStraightener 0 1 z : ℂ).re = _
  rw [circleStraightener_coe]
  simp only [Complex.sub_re, Complex.neg_re, Complex.inv_re, Complex.ofReal_re,
    Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.normSq_apply, zero_add]
  simp only [UpperHalfPlane.re, UpperHalfPlane.im]
  have hd : ((z : ℂ).re - 1) ^ 2 + (z : ℂ).im ^ 2 ≠ 0 := by
    have hzpos : 0 < (z : ℂ).im := z.im_pos
    nlinarith [hzpos, sq_nonneg ((z : ℂ).re - 1)]
  simp only [← pow_two]
  field_simp [hd]
  ring

theorem unit_circleStraightener_positive_iff (z : H2) :
    0 ≤ (circleStraightener 0 1 z).re ↔ z.re ^ 2 + z.im ^ 2 ≤ 1 := by
  rw [unit_circleStraightener_real_formula]
  have hd : 0 < 2 * ((z.re - 1) ^ 2 + z.im ^ 2) := by
    nlinarith [z.im_pos, sq_nonneg (z.re - 1)]
  rw [le_div_iff₀ hd]
  constructor <;> intro h <;> nlinarith

theorem unit_circleStraightener_negative_iff (z : H2) :
    (circleStraightener 0 1 z).re ≤ 0 ↔ 1 ≤ z.re ^ 2 + z.im ^ 2 := by
  rw [unit_circleStraightener_real_formula]
  have hd : 0 < 2 * ((z.re - 1) ^ 2 + z.im ^ 2) := by
    nlinarith [z.im_pos, sq_nonneg (z.re - 1)]
  rw [div_le_iff₀ hd]
  constructor <;> intro h <;> nlinarith

theorem metric_segment_in_unit_semicircle_inside (a b z : H2)
    (ha : a.re ^ 2 + a.im ^ 2 ≤ 1) (hb : b.re ^ 2 + b.im ^ 2 ≤ 1)
    (hz : dist a z + dist z b = dist a b) : z.re ^ 2 + z.im ^ 2 ≤ 1 := by
  apply (unit_circleStraightener_positive_iff z).mp
  apply metric_segment_in_positive_vertical_halfplane
    (circleStraightener 0 1 a) (circleStraightener 0 1 b) (circleStraightener 0 1 z)
    ((unit_circleStraightener_positive_iff a).mpr ha)
    ((unit_circleStraightener_positive_iff b).mpr hb)
  simpa only [(circleStraightener 0 1).dist_eq] using hz

theorem metric_segment_in_unit_semicircle_outside (a b z : H2)
    (ha : 1 ≤ a.re ^ 2 + a.im ^ 2) (hb : 1 ≤ b.re ^ 2 + b.im ^ 2)
    (hz : dist a z + dist z b = dist a b) : 1 ≤ z.re ^ 2 + z.im ^ 2 := by
  apply (unit_circleStraightener_negative_iff z).mp
  apply metric_segment_in_negative_vertical_halfplane
    (circleStraightener 0 1 a) (circleStraightener 0 1 b) (circleStraightener 0 1 z)
    ((unit_circleStraightener_negative_iff a).mpr ha)
    ((unit_circleStraightener_negative_iff b).mpr hb)
  simpa only [(circleStraightener 0 1).dist_eq] using hz

end CurveComplex.Hyperbolic
