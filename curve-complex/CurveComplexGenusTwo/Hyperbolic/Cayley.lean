import Mathlib

namespace CurveComplex.Hyperbolic

open scoped UpperHalfPlane

abbrev H2 := UpperHalfPlane

theorem cayley_mem_closedBall (z : H2) :
    ((z : ℂ) - Complex.I) / ((z : ℂ) + Complex.I) ∈
      Metric.closedBall (0 : ℂ) 1 := by
  have hi : 0 < (z : ℂ).im := z.im_pos
  have hden : 0 < Complex.normSq ((z : ℂ) + Complex.I) := by
    rw [Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
      add_zero]
    have : 0 < (z : ℂ).im + 1 := by linarith
    nlinarith [sq_nonneg (z : ℂ).re, sq_pos_of_pos this]
  have hsq : Complex.normSq ((z : ℂ) - Complex.I) ≤
      Complex.normSq ((z : ℂ) + Complex.I) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
      sub_zero, add_zero]
    nlinarith
  rw [Metric.mem_closedBall, dist_zero_right]
  rw [Complex.norm_def, Complex.normSq_div]
  rw [Real.sqrt_div (Complex.normSq_nonneg _)]
  apply (div_le_iff₀ (Real.sqrt_pos.2 hden)).2
  simpa using Real.sqrt_le_sqrt hsq

theorem cayley_mem_ball (z : H2) :
    ((z : ℂ) - Complex.I) / ((z : ℂ) + Complex.I) ∈
      Metric.ball (0 : ℂ) 1 := by
  have hi : 0 < (z : ℂ).im := z.im_pos
  have hden : 0 < Complex.normSq ((z : ℂ) + Complex.I) := by
    rw [Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
      add_zero]
    have : 0 < (z : ℂ).im + 1 := by linarith
    nlinarith [sq_nonneg (z : ℂ).re, sq_pos_of_pos this]
  have hsq : Complex.normSq ((z : ℂ) - Complex.I) <
      Complex.normSq ((z : ℂ) + Complex.I) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
      sub_zero, add_zero]
    nlinarith
  rw [Metric.mem_ball, dist_zero_right]
  rw [Complex.norm_def, Complex.normSq_div]
  rw [Real.sqrt_div (Complex.normSq_nonneg _)]
  apply (div_lt_iff₀ (Real.sqrt_pos.2 hden)).2
  simpa using Real.sqrt_lt_sqrt (Complex.normSq_nonneg _) hsq

noncomputable def cayley (z : H2) : Metric.closedBall (0 : ℂ) 1 :=
  ⟨((z : ℂ) - Complex.I) / ((z : ℂ) + Complex.I),
    cayley_mem_closedBall z⟩

theorem cayley_injective : Function.Injective cayley := by
  intro z w h
  apply UpperHalfPlane.coe_injective
  have hz : (z : ℂ) + Complex.I ≠ 0 := by
    intro hz
    have hi : 0 < (z : ℂ).im := z.im_pos
    have hh : (z : ℂ).im + 1 = 0 := by
      have := congrArg Complex.im hz
      simpa using this
    linarith
  have hw : (w : ℂ) + Complex.I ≠ 0 := by
    intro hw
    have hi : 0 < (w : ℂ).im := w.im_pos
    have hh : (w : ℂ).im + 1 = 0 := by
      have := congrArg Complex.im hw
      simpa using this
    linarith
  have heq : ((z : ℂ) - Complex.I) / ((z : ℂ) + Complex.I) =
      ((w : ℂ) - Complex.I) / ((w : ℂ) + Complex.I) :=
    congrArg Subtype.val h
  field_simp [hz, hw] at heq
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  apply (mul_left_cancel₀ hI)
  linear_combination (1 / 2 : ℂ) * heq

theorem cayley_continuous : Continuous cayley := by
  apply Continuous.subtype_mk
  apply Continuous.div
  · exact UpperHalfPlane.continuous_coe.sub continuous_const
  · exact UpperHalfPlane.continuous_coe.add continuous_const
  · intro z
    have hi : 0 < (z : ℂ).im := z.im_pos
    intro hz
    have hh := congrArg Complex.im hz
    simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at hh
    linarith

theorem cayley_inverse_im_pos (w : ℂ)
    (hw : w ∈ Metric.ball (0 : ℂ) 1) :
    0 < (Complex.I * (1 + w) / (1 - w)).im := by
  have hn : ‖w‖ < 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using hw
  have hsq : w.re ^ 2 + w.im ^ 2 < 1 := by
    have hnormSq := Complex.normSq_eq_norm_sq w
    rw [Complex.normSq_apply] at hnormSq
    nlinarith [norm_nonneg w]
  have hden : 0 < Complex.normSq (1 - w) := by
    rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, zero_sub]
    nlinarith [sq_nonneg (1 - w.re), sq_nonneg w.im]
  rw [Complex.div_im]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
    Complex.sub_re, Complex.sub_im, zero_mul, one_mul, zero_add,
    zero_sub, neg_mul]
  rw [← sub_div]
  apply div_pos
  · nlinarith
  · exact hden

noncomputable def cayleyInverse
    (w : Metric.ball (0 : ℂ) 1) : H2 :=
  ⟨Complex.I * (1 + (w : ℂ)) / (1 - (w : ℂ)),
    cayley_inverse_im_pos w.val w.property⟩

theorem one_sub_ball_ne_zero (w : Metric.ball (0 : ℂ) 1) :
    (1 : ℂ) - w ≠ 0 := by
  have hn : ‖(w : ℂ)‖ < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using w.property
  intro h
  have heq : (w : ℂ) = 1 := sub_eq_zero.mp h |>.symm
  rw [heq] at hn
  norm_num at hn

theorem cayleyInverse_cayley (z : H2) :
    cayleyInverse ⟨(cayley z : ℂ), cayley_mem_ball z⟩ = z := by
  apply UpperHalfPlane.coe_injective
  have hz : (z : ℂ) + Complex.I ≠ 0 := by
    intro hz
    have hi : 0 < (z : ℂ).im := z.im_pos
    have hh := congrArg Complex.im hz
    simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at hh
    linarith
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  dsimp [cayleyInverse, cayley]
  field_simp [hz, hI]
  ring

theorem cayley_cayleyInverse (w : Metric.ball (0 : ℂ) 1) :
    (cayley (cayleyInverse w) : ℂ) = w := by
  have hw := one_sub_ball_ne_zero w
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  dsimp [cayley, cayleyInverse]
  field_simp [hw, hI]
  ring

theorem cayleyInverse_continuous : Continuous cayleyInverse := by
  apply Continuous.upperHalfPlaneMk
  · apply Continuous.div
    · exact continuous_const.mul (continuous_const.add continuous_subtype_val)
    · exact continuous_const.sub continuous_subtype_val
    · exact one_sub_ball_ne_zero

noncomputable def cayleyOpen (z : H2) : Metric.ball (0 : ℂ) 1 :=
  ⟨(cayley z : ℂ), cayley_mem_ball z⟩

noncomputable def cayleyHomeomorph :
    H2 ≃ₜ Metric.ball (0 : ℂ) 1 where
  toFun := cayleyOpen
  invFun := cayleyInverse
  left_inv := cayleyInverse_cayley
  right_inv := by
    intro w
    apply Subtype.ext
    exact cayley_cayleyInverse w
  continuous_toFun := by
    exact Continuous.subtype_mk
      (continuous_subtype_val.comp cayley_continuous) _
  continuous_invFun := cayleyInverse_continuous

end CurveComplex.Hyperbolic
