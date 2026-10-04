import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualPuncturedPlaneGermLogarithm
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
/-- Actual complex log interpolation preserves a uniform endpoint norm bound.
This supplies chart-target membership for a geometric germ redraw. -/
theorem actual_complex_log_affine_norm_le
    (a b : ℂ) (τ : unitInterval) :
    ‖Complex.exp ((1-(τ:ℝ)) • a+(τ:ℝ) • b)‖≤
      max ‖Complex.exp a‖ ‖Complex.exp b‖ := by
  have hre : (((1-(τ:ℝ)) • a+(τ:ℝ) • b):ℂ).re ≤ max a.re b.re := by
    simp only [Complex.add_re,Complex.smul_re]
    have h0 := le_max_left a.re b.re
    have h1 := le_max_right a.re b.re
    simp only [smul_eq_mul]
    have h0w := mul_nonneg (sub_nonneg.mpr τ.property.2) (sub_nonneg.mpr h0)
    have h1w := mul_nonneg τ.property.1 (sub_nonneg.mpr h1)
    nlinarith
  rw [Complex.norm_exp,Complex.norm_exp,Complex.norm_exp]
  apply (Real.exp_le_exp.mpr hre).trans
  rcases le_total a.re b.re with hab | hba
  · rw [max_eq_right hab,max_eq_right (Real.exp_le_exp.mpr hab)]
  · rw [max_eq_left hba,max_eq_left (Real.exp_le_exp.mpr hba)]
/-- An actual small complex coordinate belongs to the literal closed square
contained in the produced source loop-base chart. -/
theorem actual_complex_unit_ball_plane_square
    (z : ℂ) (hz : ‖z‖≤1) :
    ArcFinitePosition.planeComplexLinearEquiv.symm z ∈ Plane.closedSquare 0 1 := by
  apply mem_closedSquare_zero_one.mpr
  apply max_le_iff.mpr
  constructor
  · change |z.re|≤1
    exact Complex.abs_re_le_norm z |>.trans hz
  · change |z.im|≤1
    exact Complex.abs_im_le_norm z |>.trans hz
/-- Real-axis contacts of an actual exponent are EXACTLY its integer-π
phase levels, including both old-loop germ branches. -/
theorem actual_complex_exponential_real_axis_iff (z : ℂ) :
    (Complex.exp z).im=0 ↔ ∃ k : ℤ, z.im=(k:ℝ)*Real.pi := by
  rw [Complex.exp_im,mul_eq_zero]
  simp only [Real.exp_ne_zero,false_or,Real.sin_eq_zero_iff]
  exact ⟨fun ⟨k,hk⟩ => ⟨k,hk.symm⟩,fun ⟨k,hk⟩ => ⟨k,hk.symm⟩⟩
end CurveComplex.HyperellipticModel
