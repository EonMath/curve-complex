import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactVertexQuarterClosure

namespace CurveComplex.Hyperbolic
open Set Topology

noncomputable def unitSemicircleParam (t : ℝ) : H2 :=
  UpperHalfPlane.mk
    (((t / Real.sqrt (1 + t ^ 2) : ℝ) : ℂ) +
      ((1 / Real.sqrt (1 + t ^ 2) : ℝ) : ℂ) * Complex.I)
    (by
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, Complex.I_re, zero_mul, mul_one, zero_add, add_zero]
      exact div_pos (by norm_num) (Real.sqrt_pos.mpr (by positivity)))

@[simp]
theorem unitSemicircleParam_re (t : ℝ) :
    (unitSemicircleParam t).re = t / Real.sqrt (1 + t ^ 2) := by
  simp [unitSemicircleParam, UpperHalfPlane.re]

@[simp]
theorem unitSemicircleParam_im (t : ℝ) :
    (unitSemicircleParam t).im = 1 / Real.sqrt (1 + t ^ 2) := by
  simp [unitSemicircleParam, UpperHalfPlane.im]

theorem unitSemicircleParam_normSq (t : ℝ) :
    (unitSemicircleParam t).re ^ 2 + (unitSemicircleParam t).im ^ 2 = 1 := by
  rw [unitSemicircleParam_re, unitSemicircleParam_im]
  have hd : Real.sqrt (1 + t ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hs := Real.sq_sqrt (show 0 ≤ 1 + t ^ 2 by positivity)
  field_simp
  nlinarith [hs]

theorem unitSemicircleParam_continuous : Continuous unitSemicircleParam := by
  apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
  change Continuous (fun t : ℝ =>
    ((t / Real.sqrt (1 + t ^ 2) : ℝ) : ℂ) +
      ((1 / Real.sqrt (1 + t ^ 2) : ℝ) : ℂ) * Complex.I)
  have hd : Continuous (fun t : ℝ => Real.sqrt (1 + t ^ 2)) := by fun_prop
  have hn : ∀ t : ℝ, Real.sqrt (1 + t ^ 2) ≠ 0 :=
    fun t => ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  exact (Complex.continuous_ofReal.comp (continuous_id.div hd hn)).add
    ((Complex.continuous_ofReal.comp (continuous_const.div hd hn)).mul continuous_const)

theorem unit_circle_point_of_either_sign_in_ball (p : H2)
    (hp : p.re = 0) (hi : p.im = 1) (r : ℝ) (hr : 0 < r) (positive : Bool) :
    ∃ z ∈ Metric.ball p r, z.re ^ 2 + z.im ^ 2 = 1 ∧
      (if positive then 0 < z.re else z.re < 0) := by
  have hzero : unitSemicircleParam 0 = p := by
    apply UpperHalfPlane.ext_re_im
    · simpa using hp.symm
    · simpa using hi.symm
  have hopen : IsOpen (unitSemicircleParam ⁻¹' Metric.ball p r) :=
    Metric.isOpen_ball.preimage unitSemicircleParam_continuous
  have h0 : (0 : ℝ) ∈ unitSemicircleParam ⁻¹' Metric.ball p r := by
    rw [Set.mem_preimage, hzero]
    exact Metric.mem_ball_self hr
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen 0 h0
  have ht : 0 < δ / 2 := by linarith
  cases positive
  · refine ⟨unitSemicircleParam (-(δ / 2)), hball ?_,
      unitSemicircleParam_normSq _, ?_⟩
    · simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_neg]
      rw [abs_of_pos ht]
      linarith
    · change (unitSemicircleParam (-(δ / 2))).re < 0
      rw [unitSemicircleParam_re]
      exact div_neg_of_neg_of_pos (neg_neg_of_pos ht) (Real.sqrt_pos.mpr (by positivity))
  · refine ⟨unitSemicircleParam (δ / 2), hball ?_,
      unitSemicircleParam_normSq _, ?_⟩
    · simp only [Metric.mem_ball, Real.dist_eq, sub_zero]
      rw [abs_of_pos ht]
      linarith
    · change 0 < (unitSemicircleParam (δ / 2)).re
      rw [unitSemicircleParam_re]
      exact div_pos ht (Real.sqrt_pos.mpr (by positivity))

theorem vertical_axis_point_of_either_side_in_ball (p : H2)
    (hp : p.re = 0) (hi : p.im = 1) (r : ℝ) (hr : 0 < r) (inner : Bool) :
    ∃ z ∈ Metric.ball p r, z.re = 0 ∧
      (if inner then z.im < 1 else 1 < z.im) := by
  have hzero : verticalPath 0 = p := by
    apply UpperHalfPlane.ext_re_im
    · simpa [verticalPath] using hp.symm
    · simpa [verticalPath] using hi.symm
  have hopen : IsOpen (verticalPath ⁻¹' Metric.ball p r) :=
    Metric.isOpen_ball.preimage verticalPath_isometry.continuous
  have h0 : (0 : ℝ) ∈ verticalPath ⁻¹' Metric.ball p r := by
    rw [Set.mem_preimage, hzero]
    exact Metric.mem_ball_self hr
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen 0 h0
  have ht : 0 < δ / 2 := by linarith
  cases inner
  · refine ⟨verticalPath (δ / 2), hball ?_, by simp [verticalPath], ?_⟩
    · simp only [Metric.mem_ball, Real.dist_eq, sub_zero]
      rw [abs_of_pos ht]
      linarith
    · change 1 < Real.exp (δ / 2)
      exact Real.one_lt_exp_iff.mpr ht
  · refine ⟨verticalPath (-(δ / 2)), hball ?_, by simp [verticalPath], ?_⟩
    · simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_neg]
      rw [abs_of_pos ht]
      linarith
    · change Real.exp (-(δ / 2)) < 1
      exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht)

end CurveComplex.Hyperbolic
