import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ConstantSpeedHyperbolicSegmentCandidate

namespace CurveComplex.Hyperbolic
open Set Topology MeasureTheory
open MeasureTheory.Measure
open scoped NNReal ENNReal MeasureTheory

theorem hyperbolic_hexagon_edge_hausdorff_area_zero (P : Hexagon) (i : Fin 6) :
    Measure.hausdorffMeasure 2 (P.edge i) = 0 := by
  have hne : P.vertex i ≠ P.vertex (i+1) := P.injective.ne (by fin_cases i <;> decide)
  obtain ⟨f, _, _, _, _, himage, hdist⟩ := metric_segment_has_constant_speed_parametrization
    (P.vertex i) (P.vertex (i+1)) hne
  have hL : LipschitzWith ⟨dist (P.vertex i) (P.vertex (i+1)), dist_nonneg⟩ f := by
    apply LipschitzWith.of_dist_le_mul
    intro t u
    rw [hdist]
    rfl
  have hfinite : (Measure.hausdorffMeasure 1 : Measure ℝ) (Icc 0 1) ≠ ∞ := by
    rw [hausdorffMeasure_real, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hzero : (Measure.hausdorffMeasure 2 : Measure ℝ) (Icc 0 1) = 0 :=
    (hausdorffMeasure_zero_or_top (by norm_num : (1 : ℝ) < 2) (Icc 0 1)).resolve_right hfinite
  have hm := hL.hausdorffMeasure_image_le (d := 2) (by norm_num) (Icc 0 1)
  rw [hzero, mul_zero] at hm
  apply le_antisymm _ (by positivity)
  simpa only [himage, Hexagon.edge] using hm

theorem hyperbolic_polygon_frontier_hausdorff_area_zero {P : Hexagon} (R : HexagonRegion P) :
    Measure.hausdorffMeasure 2 (frontier R.interior) = 0 := by
  rw [R.boundary_is_edges]
  exact measure_iUnion_null fun i => hyperbolic_hexagon_edge_hausdorff_area_zero P i

theorem hyperbolic_polygon_frontier_normalized_area_zero {P : Hexagon} (R : HexagonRegion P) :
    (μHE[2] : Measure H2) (frontier R.interior) = 0 := by
  have h := hyperbolic_polygon_frontier_hausdorff_area_zero R
  unfold Measure.euclideanHausdorffMeasure
  simp only [Measure.smul_apply]
  norm_num only [Nat.cast_ofNat] at *
  rw [h, smul_zero]

theorem hyperbolic_closed_polygon_hausdorff_area_eq_interior {P : Hexagon} (R : HexagonRegion P) :
    Measure.hausdorffMeasure 2 (closure R.interior) = Measure.hausdorffMeasure 2 R.interior := by
  apply le_antisymm _ (measure_mono subset_closure)
  have h := measure_union_le (μ := Measure.hausdorffMeasure 2) R.interior (frontier R.interior)
  rw [hyperbolic_polygon_frontier_hausdorff_area_zero R, add_zero] at h
  have hc : R.interior ∪ frontier R.interior = closure R.interior :=
    (closure_eq_self_union_frontier R.interior).symm
  rwa [hc] at h

theorem hyperbolic_closed_polygon_normalized_area_eq_interior {P : Hexagon} (R : HexagonRegion P) :
    (μHE[2] : Measure H2) (closure R.interior) = (μHE[2] : Measure H2) R.interior := by
  have h := hyperbolic_closed_polygon_hausdorff_area_eq_interior R
  unfold Measure.euclideanHausdorffMeasure
  simp only [Measure.smul_apply]
  norm_num only [Nat.cast_ofNat] at *
  rw [h]

end CurveComplex.Hyperbolic
