import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.HyperbolicPolygonBoundaryAreaCandidate
import CurveComplexGenusTwo.Hyperbolic.CompactDoubleTopology

namespace CurveComplex.Hyperbolic
open Set Topology MeasureTheory
open scoped NNReal ENNReal MeasureTheory

set_option maxHeartbeats 800000 in
theorem compact_polygon_double_hausdorff_area {P : Hexagon} (R : HexagonRegion P) :
    let G := Metric.GlueSpace (boundaryInclusion_isometry R) (boundaryInclusion_isometry R)
    letI : MeasurableSpace G := borel G
    letI : BorelSpace G := ⟨rfl⟩
    (Measure.hausdorffMeasure 2 : Measure G) univ =
      2 * (Measure.hausdorffMeasure 2 : Measure H2) R.interior := by
  let G := Metric.GlueSpace (boundaryInclusion_isometry R) (boundaryInclusion_isometry R)
  letI : MeasurableSpace G := borel G
  letI : BorelSpace G := ⟨rfl⟩
  let L : ClosedPolygon R → G := Metric.toGlueL (boundaryInclusion_isometry R) (boundaryInclusion_isometry R)
  let Q : ClosedPolygon R → G := Metric.toGlueR (boundaryInclusion_isometry R) (boundaryInclusion_isometry R)
  have hL : Isometry L := Metric.toGlueL_isometry _ _
  have hQ : Isometry Q := Metric.toGlueR_isometry _ _
  have hcover : range L ∪ range Q = (univ : Set G) := by
    apply eq_univ_iff_forall.mpr
    intro z
    refine Quotient.inductionOn z ?_
    intro v
    cases v with
    | inl x => exact Or.inl ⟨x, rfl⟩
    | inr y => exact Or.inr ⟨y, rfl⟩
  let t : Set (ClosedPolygon R) := {x | (x : H2) ∈ frontier R.interior}
  have him : Subtype.val '' t = frontier R.interior := by
    ext z; constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro hz; exact ⟨⟨z, frontier_subset_closure hz⟩, hz, rfl⟩
  have htzero : (Measure.hausdorffMeasure 2 : Measure (ClosedPolygon R)) t = 0 := by
    have h := (isometry_subtype_coe : Isometry (Subtype.val : ClosedPolygon R → H2)).hausdorffMeasure_image
      (d := 2) (Or.inl (by norm_num)) t
    rw [him, hyperbolic_polygon_frontier_hausdorff_area_zero R] at h
    exact h.symm
  have hcross : range L ∩ range Q ⊆ L '' t := by
    rintro z ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    have hxy := (polygon_double_cross_copy_eq_iff R x y).mp (hx.trans hy.symm)
    exact ⟨x, hxy.2, hx⟩
  have hzero : (Measure.hausdorffMeasure 2 : Measure G) (range L ∩ range Q) = 0 := by
    apply measure_mono_null hcross
    rw [hL.hausdorffMeasure_image (Or.inl (by norm_num)), htzero]
  have hQmeas : MeasurableSet (range Q) := by
    have hcompact : IsCompact (Q '' univ) := isCompact_univ.image hQ.continuous
    simpa only [image_univ] using hcompact.isClosed.measurableSet
  have hmass : (Measure.hausdorffMeasure 2 : Measure (ClosedPolygon R)) univ =
      (Measure.hausdorffMeasure 2 : Measure H2) R.interior := by
    have h := (isometry_subtype_coe : Isometry (Subtype.val : ClosedPolygon R → H2)).hausdorffMeasure_image
      (d := 2) (Or.inl (by norm_num)) univ
    have hh : (Measure.hausdorffMeasure 2 : Measure H2) (closure R.interior) =
        (Measure.hausdorffMeasure 2 : Measure (ClosedPolygon R)) univ := by
      simpa only [image_univ, Subtype.range_coe_subtype, ofPred_mem_eq] using h
    exact hh.symm.trans (hyperbolic_closed_polygon_hausdorff_area_eq_interior R)
  have hleft := hL.hausdorffMeasure_image (d := 2) (Or.inl (by norm_num)) univ
  have hright := hQ.hausdorffMeasure_image (d := 2) (Or.inl (by norm_num)) univ
  simp only [image_univ, hmass] at hleft hright
  have h := measure_union_add_inter (μ := Measure.hausdorffMeasure 2) (range L) hQmeas
  rw [hcover, hzero, add_zero, hleft, hright, ← two_mul] at h
  exact h

theorem compact_polygon_double_normalized_area {P : Hexagon} (R : HexagonRegion P) :
    let G := Metric.GlueSpace (boundaryInclusion_isometry R) (boundaryInclusion_isometry R)
    letI : MeasurableSpace G := borel G
    letI : BorelSpace G := ⟨rfl⟩
    (μHE[2] : Measure G) univ = 2 * (μHE[2] : Measure H2) R.interior := by
  let G := Metric.GlueSpace (boundaryInclusion_isometry R) (boundaryInclusion_isometry R)
  letI : MeasurableSpace G := borel G
  letI : BorelSpace G := ⟨rfl⟩
  have h := compact_polygon_double_hausdorff_area R
  unfold Measure.euclideanHausdorffMeasure
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  norm_num only [Nat.cast_ofNat] at *
  rw [h]
  ac_rfl

end CurveComplex.Hyperbolic
