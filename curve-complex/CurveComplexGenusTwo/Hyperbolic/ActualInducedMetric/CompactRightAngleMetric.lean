import CurveComplexGenusTwo.Hyperbolic.FiniteRightHexagon
namespace CurveComplex.Hyperbolic

private theorem right_angle_coordinate_polynomial (q p r : H2) (h : IsRightAngle q p r) :
    (p.im ^ 2 - q.im ^ 2 - (q.re - p.re)^2) *
      (p.im ^ 2 - r.im ^ 2 - (r.re - p.re)^2) +
      4 * p.im ^ 2 * (q.re - p.re) * (r.re - p.re) = 0 := by
  by_cases hq : p.re = q.re <;> by_cases hr : p.re = r.re
  · have htq : geodesicTangent p q = Complex.I := ite_eq_left hq
    have htr : geodesicTangent p r = Complex.I := ite_eq_left hr
    unfold IsRightAngle at h
    rw [htq, htr] at h
    norm_num [Complex.star_def] at h
  · have hr' : r.re - p.re ≠ 0 := sub_ne_zero.mpr (Ne.symm hr)
    change (p : ℂ).re = (q : ℂ).re at hq
    change (p : ℂ).re ≠ (r : ℂ).re at hr
    simp only [IsRightAngle, geodesicTangent, ite_eq_left hq, ite_eq_right hr,
      Complex.star_def, Complex.conj_I, Complex.mul_re, Complex.mul_im,
      Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im] at h
    simp only [zero_mul, one_mul, mul_zero, mul_one, sub_zero, zero_sub, neg_neg, zero_add, add_zero] at h
    replace h : p.re - semicircleCentre p r = 0 := by convert h using 1 <;> simp only [UpperHalfPlane.re] <;> ring
    unfold semicircleCentre at h
    simp only [Complex.normSq_apply] at h
    simp only [UpperHalfPlane.re, UpperHalfPlane.im] at *
    field_simp at h
    rw [← hq]
    nlinarith [h]
  · have hq' : q.re - p.re ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
    change (p : ℂ).re ≠ (q : ℂ).re at hq
    change (p : ℂ).re = (r : ℂ).re at hr
    simp only [IsRightAngle, geodesicTangent, ite_eq_right hq, ite_eq_left hr,
      star_mul', Complex.star_def, Complex.conj_I, Complex.conj_re, Complex.conj_im,
      Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im] at h
    simp only [zero_mul, one_mul, mul_zero, mul_one, sub_zero, zero_sub, neg_neg, zero_add, add_zero] at h
    replace h : p.re - semicircleCentre p q = 0 := by convert h using 1 <;> simp only [UpperHalfPlane.re] <;> ring
    unfold semicircleCentre at h
    simp only [Complex.normSq_apply] at h
    simp only [UpperHalfPlane.re, UpperHalfPlane.im] at *
    field_simp at h
    rw [← hr]
    nlinarith [h]
  · have hq' : q.re - p.re ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
    have hr' : r.re - p.re ≠ 0 := sub_ne_zero.mpr (Ne.symm hr)
    change (p : ℂ).re ≠ (q : ℂ).re at hq
    change (p : ℂ).re ≠ (r : ℂ).re at hr
    simp only [IsRightAngle, geodesicTangent, ite_eq_right hq, ite_eq_right hr,
      star_mul', star_sub, Complex.star_def, Complex.conj_I, Complex.conj_ofReal,
      Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero, sub_zero,
      zero_sub, neg_mul, neg_neg, neg_add_rev] at h
    unfold semicircleCentre at h
    simp only [Complex.normSq_apply] at h
    simp only [UpperHalfPlane.re, UpperHalfPlane.im] at *
    field_simp at h
    nlinarith [h]

theorem right_angle_hyperbolic_pythagoras (q p r : H2) (h : IsRightAngle q p r) :
    Real.cosh (dist q r) = Real.cosh (dist p q) * Real.cosh (dist p r) := by
  have hp := right_angle_coordinate_polynomial q p r h
  rw [UpperHalfPlane.cosh_dist', UpperHalfPlane.cosh_dist', UpperHalfPlane.cosh_dist']
  field_simp
  nlinarith [hp]
theorem right_angle_unit_semicircle_of_normalized_isometry
    (q p r : H2) (h : IsRightAngle q p r) (e : H2 ≃ᵢ H2)
    (hp_re : (e p).re = 0) (hp_im : (e p).im = 1)
    (hq_re : (e q).re = 0) (hqp : q ≠ p) :
    (e r).re ^ 2 + (e r).im ^ 2 = 1 := by
  have h := right_angle_hyperbolic_pythagoras q p r h
  rw [← e.dist_eq q r, ← e.dist_eq p q, ← e.dist_eq p r] at h
  rw [UpperHalfPlane.cosh_dist', UpperHalfPlane.cosh_dist',
    UpperHalfPlane.cosh_dist'] at h
  rw [hp_re, hp_im, hq_re] at h
  have hqi : (e q).im ≠ 1 := by
    intro heq
    apply hqp
    apply e.injective
    apply UpperHalfPlane.ext_re_im
    · exact hq_re.trans hp_re.symm
    · exact heq.trans hp_im.symm
  have hq2 : (e q).im ^ 2 ≠ 1 := by
    intro hs
    apply hqi
    nlinarith [(e q).im_pos]
  field_simp at h
  have hf : ((e q).im ^ 2 - 1) *
      ((e r).re ^ 2 + (e r).im ^ 2 - 1) = 0 := by nlinarith [h]
  have hr := (mul_eq_zero.mp hf).resolve_left (sub_ne_zero.mpr hq2)
  linarith
end CurveComplex.Hyperbolic
