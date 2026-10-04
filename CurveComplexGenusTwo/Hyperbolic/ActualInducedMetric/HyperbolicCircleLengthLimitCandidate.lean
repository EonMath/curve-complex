import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.EuclideanCircleHausdorffCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.HyperbolicCircleHausdorffComparisonCandidate

namespace CurveComplex.Hyperbolic
open Set Topology Filter MeasureTheory
open scoped NNReal ENNReal UpperHalfPlane

set_option maxHeartbeats 800000 in
theorem upperHalfPlane_I_circle_length_squeeze (r : ℝ) (hr : 0 < r)
    (hsmall : Real.sinh r + Real.cosh r - 1 < 1) :
    localLowerSlope UpperHalfPlane.I (Real.sinh r + Real.cosh r - 1) *
      (2 * Real.pi * Real.sinh r / r) ≤
        (Measure.hausdorffMeasure 1 (Metric.sphere UpperHalfPlane.I r)).toReal / r ∧
    (Measure.hausdorffMeasure 1 (Metric.sphere UpperHalfPlane.I r)).toReal / r ≤
      localUpperSlope UpperHalfPlane.I (Real.sinh r + Real.cosh r - 1) *
        (2 * Real.pi * Real.sinh r / r) := by
  let δ := Real.sinh r + Real.cosh r - 1
  have hδ : 0 ≤ δ := by dsimp [δ]; linarith [Real.sinh_pos_iff.mpr hr, Real.one_le_cosh r]
  have hδsmall : δ < UpperHalfPlane.I.im := by simpa [δ] using hsmall
  obtain ⟨hl, hu⟩ := upperHalfPlane_local_hausdorff_length_squeeze UpperHalfPlane.I hδ hδsmall
    (Metric.sphere UpperHalfPlane.I r) (upperHalfPlane_I_sphere_in_small_euclidean_ball r hr.le)
  have hcircle : Measure.hausdorffMeasure 1 (UpperHalfPlane.coe '' Metric.sphere UpperHalfPlane.I r) =
      ENNReal.ofReal (2 * Real.pi * Real.sinh r) := by
    rw [UpperHalfPlane.image_coe_sphere]
    simp only [UpperHalfPlane.I_im, one_mul]
    exact euclidean_circle_hausdorff_length _ _ (Real.sinh_pos_iff.mpr hr)
  rw [hcircle] at hl hu
  have hμfinite : Measure.hausdorffMeasure 1 (Metric.sphere UpperHalfPlane.I r) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top) hu
  have hlu := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hμfinite) hl
  have huu := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top) hu
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofReal (by positivity :
      0 ≤ 2 * Real.pi * Real.sinh r)] at hlu huu
  change 2 * Real.pi * Real.sinh r ≤ (localLowerSlope UpperHalfPlane.I δ)⁻¹ *
    (Measure.hausdorffMeasure 1 (Metric.sphere UpperHalfPlane.I r)).toReal at hlu
  change (Measure.hausdorffMeasure 1 (Metric.sphere UpperHalfPlane.I r)).toReal ≤
    localUpperSlope UpperHalfPlane.I δ * (2 * Real.pi * Real.sinh r) at huu
  have hp : 0 < localLowerSlope UpperHalfPlane.I δ := by
    unfold localLowerSlope
    have hz : 0 < UpperHalfPlane.I.im - δ := sub_pos.mpr hδsmall
    positivity
  have hlreal := (le_inv_mul_iff₀ hp).mp hlu
  constructor
  · have h := div_le_div_of_nonneg_right hlreal hr.le
    simpa only [mul_div_assoc] using h
  · have h := div_le_div_of_nonneg_right huu hr.le
    simpa only [mul_div_assoc] using h

set_option maxHeartbeats 800000 in
theorem upperHalfPlane_I_small_circle_hausdorff_length_limit :
    Tendsto (fun r : ℝ =>
      (Measure.hausdorffMeasure 1 (Metric.sphere UpperHalfPlane.I r)).toReal / r)
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * Real.pi)) := by
  let δ : ℝ → ℝ := fun r => Real.sinh r + Real.cosh r - 1
  have hδ : Tendsto δ (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : ContinuousAt δ 0 := by dsimp [δ]; fun_prop
    simpa [δ] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hsinh : Tendsto (fun r : ℝ => Real.sinh r / r) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa [div_eq_mul_inv, mul_comm] using (Real.hasDerivAt_sinh 0).tendsto_slope_zero_right
  have hratio : Tendsto (fun r : ℝ => 2 * Real.pi * Real.sinh r / r)
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * Real.pi)) := by
    simpa only [mul_one, mul_div_assoc] using tendsto_const_nhds.mul hsinh
  have hlo := (localLowerSlope_tendsto UpperHalfPlane.I).comp hδ
  have hhi := (localUpperSlope_tendsto UpperHalfPlane.I).comp hδ
  simp only [UpperHalfPlane.I_im, div_one] at hlo hhi
  have hl := hlo.mul hratio
  have hu := hhi.mul hratio
  simp only [one_mul] at hl hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · filter_upwards [self_mem_nhdsWithin,
      hδ.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with r hr hsmall
    exact (upperHalfPlane_I_circle_length_squeeze r hr hsmall).1
  · filter_upwards [self_mem_nhdsWithin,
      hδ.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with r hr hsmall
    exact (upperHalfPlane_I_circle_length_squeeze r hr hsmall).2

end CurveComplex.Hyperbolic
