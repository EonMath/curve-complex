import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.MetricChartSphereMeasureCandidate

namespace CurveComplex.Hyperbolic
open Set MeasureTheory
open scoped ENNReal MeasureTheory

theorem metric_chart_hausdorff_measure_image {E F : Type*}
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [MetricSpace F] [MeasurableSpace F] [BorelSpace F]
    (e : OpenPartialHomeomorph E F)
    (hmetric : ∀ y ∈ e.source, ∀ z ∈ e.source, dist y z = dist (e y) (e z))
    (s : Set E) (hs : s ⊆ e.source) (d : ℝ) (hd : 0 ≤ d) :
    Measure.hausdorffMeasure d (e '' s) = Measure.hausdorffMeasure d s := by
  let f : s → F := fun y => e y
  have hf : Isometry f := Isometry.of_dist_eq fun y z => (hmetric y (hs y.property) z (hs z.property)).symm
  have h₁ := hf.hausdorffMeasure_image (d := d) (Or.inl hd) univ
  have h₂ := (isometry_subtype_coe : Isometry (Subtype.val : s → E)).hausdorffMeasure_image
    (d := d) (Or.inl hd) univ
  have hr : range f = e '' s := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩; exact ⟨y, y.property, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨⟨y, hy⟩, rfl⟩
  simpa only [image_univ, hr, Subtype.range_coe_subtype, ofPred_mem_eq] using h₁.trans h₂.symm

theorem metric_chart_normalized_area_image {E F : Type*}
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [MetricSpace F] [MeasurableSpace F] [BorelSpace F]
    (e : OpenPartialHomeomorph E F)
    (hmetric : ∀ y ∈ e.source, ∀ z ∈ e.source, dist y z = dist (e y) (e z))
    (s : Set E) (hs : s ⊆ e.source) :
    (μHE[2] : Measure F) (e '' s) = (μHE[2] : Measure E) s := by
  have h := metric_chart_hausdorff_measure_image e hmetric s hs 2 (by norm_num)
  letI : (Measure.hausdorffMeasure 2 : Measure (EuclideanSpace ℝ (Fin 2))).IsAddHaarMeasure := by
    simpa using (MeasureTheory.isAddHaarMeasure_hausdorffMeasure
      (E := EuclideanSpace ℝ (Fin 2)))
  unfold Measure.euclideanHausdorffMeasure
  simp only [Measure.smul_apply]
  norm_num only [Nat.cast_ofNat] at *
  exact congrArg (fun t : ℝ≥0∞ =>
    (Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin 2)))
      (Measure.hausdorffMeasure 2 : Measure (EuclideanSpace ℝ (Fin 2)))) • t) h

end CurveComplex.Hyperbolic
