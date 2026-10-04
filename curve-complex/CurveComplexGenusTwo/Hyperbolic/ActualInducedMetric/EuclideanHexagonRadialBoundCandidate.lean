import Mathlib

namespace CurveComplex.Hyperbolic

set_option maxHeartbeats 1000000 in
theorem euclidean_six_support_radial_bound (x y L : ℝ)
    (h₀ : 3*x + Real.sqrt 3*y ≤ 3*L)
    (h₁ : 2*Real.sqrt 3*y ≤ 3*L)
    (h₂ : -3*x + Real.sqrt 3*y ≤ 3*L)
    (h₃ : -3*x - Real.sqrt 3*y ≤ 3*L)
    (h₄ : -2*Real.sqrt 3*y ≤ 3*L)
    (h₅ : 3*x - Real.sqrt 3*y ≤ 3*L) : x^2+y^2 ≤ L^2 := by
  have hs : (Real.sqrt 3)^2 = 3 := by norm_num
  have hp : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have ha : 3*|x| + Real.sqrt 3*|y| ≤ 3*L := by
    by_cases hx : 0 ≤ x <;> by_cases hy : 0 ≤ y
    · simpa only [abs_of_nonneg hx, abs_of_nonneg hy] using h₀
    · simpa only [abs_of_nonneg hx, abs_of_neg (lt_of_not_ge hy), mul_neg, neg_mul, sub_eq_add_neg] using h₅
    · simpa only [abs_of_neg (lt_of_not_ge hx), abs_of_nonneg hy, mul_neg, neg_mul, sub_eq_add_neg] using h₂
    · simpa only [abs_of_neg (lt_of_not_ge hx), abs_of_neg (lt_of_not_ge hy), mul_neg, neg_mul, sub_eq_add_neg] using h₃
  have hb : 2*Real.sqrt 3*|y| ≤ 3*L := by
    by_cases hy : 0 ≤ y
    · simpa only [abs_of_nonneg hy] using h₁
    · simpa only [abs_of_neg (lt_of_not_ge hy), mul_neg, neg_mul, sub_eq_add_neg] using h₄
  have hL : 0 ≤ L := by nlinarith [abs_nonneg x, abs_nonneg y]
  have hxs : |x|^2 = x^2 := sq_abs x
  have hys : |y|^2 = y^2 := sq_abs y
  by_cases hdom : |y| ≤ Real.sqrt 3 * |x|
  · have hm : 0 ≤ |y| * (Real.sqrt 3 * |x| - |y|) :=
      mul_nonneg (abs_nonneg y) (sub_nonneg.mpr hdom)
    have hal : |x| + |y| / Real.sqrt 3 ≤ L := by
      apply (mul_le_mul_iff_left₀ hp).mp
      have ha' := mul_le_mul_of_nonneg_left ha hp.le
      rw [add_mul, div_mul_cancel₀ _ hp.ne']
      have hh : Real.sqrt 3 * Real.sqrt 3 * |y| = 3 * |y| := by rw [← pow_two, hs]
      nlinarith [ha', hh]
    have hn : 0 ≤ |x| + |y| / Real.sqrt 3 := by positivity
    have hsq := (sq_le_sq₀ hn hL).mpr hal
    have hsq' := mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 3)
    field_simp at hsq'
    nlinarith [hm, hxs, hys, hs]
  · have hm : 0 ≤ (|y| - Real.sqrt 3*|x|) * (|y| + Real.sqrt 3*|x|) :=
      mul_nonneg (by linarith) (by positivity)
    have hbnon : 0 ≤ 2*Real.sqrt 3*|y| := by positivity
    have hsq := (sq_le_sq₀ hbnon (by positivity : 0 ≤ 3*L)).mpr hb
    nlinarith [hm, hsq, hxs, hys, hs]

end CurveComplex.Hyperbolic
