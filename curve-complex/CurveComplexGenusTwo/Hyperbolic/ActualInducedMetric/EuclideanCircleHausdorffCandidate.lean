import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.UnitSpeedCurveHausdorffCandidate

namespace CurveComplex.Hyperbolic
open Set MeasureTheory Complex
open MeasureTheory.Measure
open scoped NNReal ENNReal Interval ContDiff Pointwise

theorem euclidean_unit_circle_hausdorff_length (c : ℂ) :
    Measure.hausdorffMeasure 1 (Metric.sphere c 1) = ENNReal.ofReal (2 * Real.pi) := by
  have hinj : InjOn (circleMap c 1) (Ioo 0 (2 * Real.pi)) := by
    apply (injOn_circleMap_of_abs_sub_le' (a := 0) (b := 2 * Real.pi) (c := c) (R := 1) one_ne_zero (by simp)).mono
    exact Ioo_subset_Ico_self
  have hstrict (x : ℝ) (hx : x ∈ Ioo 0 (2 * Real.pi)) :
      ∃ v : ℂ, HasStrictDerivAt (circleMap c 1) v x ∧ ‖v‖ = 1 := by
    refine ⟨circleMap 0 1 x * Complex.I, ?_, ?_⟩
    · exact (contDiff_circleMap c 1 (n := ∞)).contDiffAt.hasStrictDerivAt'
        (hasDerivAt_circleMap c 1 x) (by simp)
    · simp [circleMap, Complex.norm_mul]
  have h := unit_speed_curve_hausdorff_length (circleMap c 1) 0 (2 * Real.pi)
    Real.two_pi_pos hinj hstrict
  letI : NullSingletonClass (Measure.hausdorffMeasure 1 : Measure ℂ) :=
    nullSingletonClass_hausdorff ℂ (by norm_num)
  have him := image_circleMap_Ioc c 1
  simp only [abs_one] at him
  rw [← him, ← Ioo_insert_right Real.two_pi_pos, Set.image_insert_eq]
  calc
    _ = Measure.hausdorffMeasure 1 (circleMap c 1 '' Ioo 0 (2 * Real.pi)) :=
      measure_congr (insert_ae_eq_self _ _)
    _ = ENNReal.ofReal (2 * Real.pi) := by simpa only [sub_zero] using h

theorem euclidean_circle_hausdorff_length (c : ℂ) (R : ℝ) (hR : 0 < R) :
    Measure.hausdorffMeasure 1 (Metric.sphere c R) = ENNReal.ofReal (2 * Real.pi * R) := by
  have hs : R • Metric.sphere (0 : ℂ) 1 = Metric.sphere (0 : ℂ) R := by
    simpa only [smul_zero, mul_one, Real.norm_eq_abs, abs_of_pos hR] using
      smul_sphere' hR.ne' (0 : ℂ) 1
  have hm := Measure.hausdorffMeasure_smul₀ (d := 1) (by norm_num) hR.ne' (Metric.sphere (0 : ℂ) 1)
  rw [hs, NNReal.rpow_one, euclidean_unit_circle_hausdorff_length] at hm
  have hzero : Measure.hausdorffMeasure 1 (Metric.sphere (0 : ℂ) R) =
      ENNReal.ofReal (2 * Real.pi * R) := by
    rw [hm]
    simp only [ENNReal.smul_def, smul_eq_mul]
    have hn : (‖R‖₊ : ℝ≥0∞) = ENNReal.ofReal R := by
      simp [← ENNReal.ofReal_coe_nnreal, Real.norm_eq_abs, abs_of_pos hR]
    rw [hn, ← ENNReal.ofReal_mul hR.le]
    congr 1; ring
  let e : ℂ ≃ᵢ ℂ := IsometryEquiv.addLeft c
  have he := e.hausdorffMeasure_image 1 (Metric.sphere (0 : ℂ) R)
  rw [e.image_sphere] at he
  have hcz : e 0 = c := by change c + 0 = c; exact add_zero c
  rw [hcz] at he
  exact he.trans hzero

end CurveComplex.Hyperbolic
