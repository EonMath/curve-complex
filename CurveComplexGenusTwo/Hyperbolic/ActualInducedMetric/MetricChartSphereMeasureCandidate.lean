import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.MetricChartSphereIsometryCandidate
import Mathlib.MeasureTheory.Measure.Hausdorff

namespace CurveComplex.Hyperbolic
open Set MeasureTheory
open scoped ENNReal

theorem hausdorff_measure_eq_of_subtype_isometry {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] (s : Set X) (t : Set Y) (e : s ≃ᵢ t) (d : ℝ) (hd : 0 ≤ d) :
    Measure.hausdorffMeasure d s = Measure.hausdorffMeasure d t := by
  have hs := (isometry_subtype_coe : Isometry (Subtype.val : s → X)).hausdorffMeasure_image
    (d := d) (Or.inl hd) Set.univ
  have ht := (isometry_subtype_coe : Isometry (Subtype.val : t → Y)).hausdorffMeasure_image
    (d := d) (Or.inl hd) Set.univ
  have he := e.hausdorffMeasure_image d Set.univ
  simp only [image_univ, Subtype.range_coe_subtype, e.surjective.range_eq] at hs ht he
  exact hs.trans (he.symm.trans ht.symm)

theorem metric_chart_small_spheres_hausdorff_measure {E : Type} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (e : OpenPartialHomeomorph E H2) (x : E) (hx : x ∈ e.source)
    (hmetric : ∀ y ∈ e.source, ∀ z ∈ e.source, dist y z = dist (e y) (e z)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε →
      Measure.hausdorffMeasure 1 (Metric.sphere x r) =
        Measure.hausdorffMeasure 1 (Metric.sphere (e x) r) := by
  obtain ⟨ε, hε, h⟩ := metric_chart_small_spheres_isometric e x hx hmetric
  refine ⟨ε, hε, ?_⟩
  intro r hr hrε
  obtain ⟨f⟩ := h r hr hrε
  exact hausdorff_measure_eq_of_subtype_isometry _ _ f 1 (by norm_num)

end CurveComplex.Hyperbolic
