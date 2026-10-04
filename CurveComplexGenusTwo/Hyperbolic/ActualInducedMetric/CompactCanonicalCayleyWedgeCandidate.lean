import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactCanonicalWedgeSideCandidate

namespace CurveComplex.Hyperbolic

theorem cayley_first_half_wedge_coordinate_iff (z : H2) :
    (0 < (cayley z : ℂ).im ∧ Real.sqrt 3*(cayley z : ℂ).im < (cayley z : ℂ).re) ↔
      (z.re < 0 ∧ 1 < z.re^2+z.im^2+2*Real.sqrt 3*z.re) := by
  let D := z.re^2+(z.im+1)^2
  have hd : 0 < D := by dsimp [D]; nlinarith [z.im_pos,sq_nonneg z.re]
  have hIm : (cayley z : ℂ).im = -2*z.re/D := by
    simp only [cayley,Complex.div_im,Complex.normSq_apply,Complex.sub_re,
      Complex.sub_im,Complex.add_re,Complex.add_im,Complex.I_re,Complex.I_im,
      sub_zero,add_zero,←pow_two]
    dsimp [D]
    field_simp
    ring
  have hRe : (cayley z : ℂ).re = (z.re^2+z.im^2-1)/D := by
    simp only [cayley,Complex.div_re,Complex.normSq_apply,Complex.sub_re,
      Complex.sub_im,Complex.add_re,Complex.add_im,Complex.I_re,Complex.I_im,
      sub_zero,add_zero,←pow_two]
    dsimp [D]
    field_simp
    ring
  have hY : 0 < (cayley z : ℂ).im ↔ z.re < 0 := by
    rw [hIm]
    constructor
    · intro h
      have h' : 0 < -2*z.re := (div_pos_iff_of_pos_right hd).mp h
      linarith
    · intro h
      apply div_pos (by linarith) hd
  have hX : Real.sqrt 3*(cayley z : ℂ).im < (cayley z : ℂ).re ↔
      1 < z.re^2+z.im^2+2*Real.sqrt 3*z.re := by
    rw [hIm,hRe]
    have he : Real.sqrt 3*(-2*z.re/D) = (Real.sqrt 3*(-2*z.re))/D := by ring
    rw [he,div_lt_div_iff_of_pos_right hd]
    constructor <;> intro h <;> linarith
  exact and_congr hY hX

end CurveComplex.Hyperbolic
