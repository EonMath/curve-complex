import CurveComplexGenusTwo.Hyperbolic.Cayley

namespace CurveComplex.Hyperbolic

private theorem one_sub_point_normSq_pos (w : Metric.ball (0 : ℂ) 1) :
    0 < Complex.normSq (1 - (w : ℂ)) := by
  rw [Complex.normSq_pos]
  exact one_sub_ball_ne_zero w

theorem cayleyInverse_re (w : Metric.ball (0 : ℂ) 1) :
    (cayleyInverse w).re =
      -2 * (w : ℂ).im / Complex.normSq (1 - (w : ℂ)) := by
  change (Complex.I * (1 + (w : ℂ)) / (1 - (w : ℂ))).re = _
  rw [Complex.div_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, zero_mul, one_mul, zero_add, zero_sub,
    neg_mul]
  ring

theorem cayleyInverse_im (w : Metric.ball (0 : ℂ) 1) :
    (cayleyInverse w).im =
      (1 - Complex.normSq (w : ℂ)) /
        Complex.normSq (1 - (w : ℂ)) := by
  change (Complex.I * (1 + (w : ℂ)) / (1 - (w : ℂ))).im = _
  rw [Complex.div_im]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, zero_mul, one_mul, zero_add, zero_sub,
    neg_mul, Complex.normSq_apply]
  ring

private theorem normSq_lt_one (w : Metric.ball (0 : ℂ) 1) :
    Complex.normSq (w : ℂ) < 1 := by
  have hw : ‖(w : ℂ)‖ < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using w.property
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg (w : ℂ)]

theorem cayleyInverse_sub (u v : Metric.ball (0 : ℂ) 1) :
    (cayleyInverse u : ℂ) - (cayleyInverse v : ℂ) =
      2 * Complex.I * ((u : ℂ) - (v : ℂ)) /
        ((1 - (u : ℂ)) * (1 - (v : ℂ))) := by
  change Complex.I * (1 + (u : ℂ)) / (1 - (u : ℂ)) -
    Complex.I * (1 + (v : ℂ)) / (1 - (v : ℂ)) = _
  field_simp [one_sub_ball_ne_zero u, one_sub_ball_ne_zero v]
  ring

theorem cayleyInverse_cosh_dist (u v : Metric.ball (0 : ℂ) 1) :
    Real.cosh (dist (cayleyInverse u) (cayleyInverse v)) =
      1 + 2 * Complex.normSq ((u : ℂ) - (v : ℂ)) /
        ((1 - Complex.normSq (u : ℂ)) *
          (1 - Complex.normSq (v : ℂ))) := by
  have hAu := (one_sub_point_normSq_pos u).ne'
  have hAv := (one_sub_point_normSq_pos v).ne'
  have hBu : 1 - Complex.normSq (u : ℂ) ≠ 0 :=
    (sub_pos.mpr (normSq_lt_one u)).ne'
  have hBv : 1 - Complex.normSq (v : ℂ) ≠ 0 :=
    (sub_pos.mpr (normSq_lt_one v)).ne'
  rw [UpperHalfPlane.cosh_dist]
  rw [Complex.dist_eq, ← Complex.normSq_eq_norm_sq]
  rw [cayleyInverse_sub, Complex.normSq_div, cayleyInverse_im,
    cayleyInverse_im]
  simp only [Complex.normSq_mul, Complex.normSq_ofReal,
    Complex.normSq_I, Complex.normSq_one]
  field_simp [hAu, hAv, hBu, hBv]
  norm_num [Complex.normSq_apply]
  ring

end CurveComplex.Hyperbolic
