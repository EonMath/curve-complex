import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.HyperbolicCircleLengthLimitCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.MetricChartSphereMeasureCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.InducedMetricConeAngleReuse

namespace CurveComplex.Hyperbolic
open Set Topology Filter MeasureTheory
open scoped UpperHalfPlane

theorem upperHalfPlane_I_cone_angle : ConeAngleAt H2 UpperHalfPlane.I (2 * Real.pi) := by
  unfold ConeAngleAt
  simpa only [Measure.hausdorffMeasure, ← OuterMeasure.coe_mkMetric] using upperHalfPlane_I_small_circle_hausdorff_length_limit

theorem metric_chart_cone_angle_at {E : Type} [MetricSpace E]
    (e : OpenPartialHomeomorph E H2) (x : E) (hx : x ∈ e.source)
    (hcenter : e x = UpperHalfPlane.I)
    (hmetric : ∀ y ∈ e.source, ∀ z ∈ e.source, dist y z = dist (e y) (e z)) :
    ConeAngleAt E x (2 * Real.pi) := by
  unfold ConeAngleAt
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  obtain ⟨ε, hε, hs⟩ := metric_chart_small_spheres_hausdorff_measure e x hx hmetric
  have heq : (fun r : ℝ => (Measure.hausdorffMeasure 1 (Metric.sphere x r)).toReal / r) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun r : ℝ => (Measure.hausdorffMeasure 1 (Metric.sphere UpperHalfPlane.I r)).toReal / r) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hε).filter_mono nhdsWithin_le_nhds] with r hr hrε
    rw [hs r hr hrε, hcenter]
  exact (tendsto_congr' heq).mpr upperHalfPlane_I_small_circle_hausdorff_length_limit

theorem compatible_metric_chart_cone_angle_at {E : Type} [TopologicalSpace E]
    (m : MetricSpace E) (ht : m.toUniformSpace.toTopologicalSpace = ‹TopologicalSpace E›)
    (e : OpenPartialHomeomorph E H2) (x : E) (hx : x ∈ e.source)
    (hcenter : e x = UpperHalfPlane.I)
    (hmetric : ∀ y ∈ e.source, ∀ z ∈ e.source, m.dist y z = dist (e y) (e z)) :
    @ConeAngleAt E m x (2 * Real.pi) := by
  cases ht
  letI : MetricSpace E := m
  exact metric_chart_cone_angle_at e x hx hcenter hmetric

end CurveComplex.Hyperbolic
