import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactCanonicalDiscSidesCandidate
import CurveComplexGenusTwo.Hyperbolic.CompactSegmentParametrization

namespace CurveComplex.Hyperbolic

theorem cayley_disc_circle_signed_polynomial (c : ℂ) (z : H2) :
    (Complex.normSq (cayley z : ℂ) - 2 * (star c * (cayley z : ℂ)).re + 1) *
      (z.re ^ 2 + (z.im + 1) ^ 2) =
    2 * ((1 - c.re) * (z.re ^ 2 + z.im ^ 2) + (1 + c.re) + 2 * c.im * z.re) := by
  have hd : z.re ^ 2 + (z.im + 1) ^ 2 ≠ 0 := by
    nlinarith [z.im_pos, sq_nonneg z.re]
  change (Complex.normSq (((z : ℂ) - Complex.I) / ((z : ℂ) + Complex.I)) -
    2 * (star c * (((z : ℂ) - Complex.I) / ((z : ℂ) + Complex.I))).re + 1) * _ = _
  rw [Complex.normSq_div]
  simp only [ Complex.div_re, Complex.div_im,
    Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.I_re, Complex.I_im, sub_zero, add_zero,
    UpperHalfPlane.re, UpperHalfPlane.im]
  simp only [← pow_two]
  field_simp [hd]
  ring

end CurveComplex.Hyperbolic
