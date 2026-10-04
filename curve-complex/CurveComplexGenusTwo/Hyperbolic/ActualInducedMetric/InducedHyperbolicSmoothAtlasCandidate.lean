import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.EuclideanMetricAtlasTransitionCandidate
import Mathlib.Geometry.Manifold.IsManifold.Basic

namespace CurveComplex.Hyperbolic
open Set
open scoped Manifold ContDiff
variable {E : Type} [MetricSpace E]

theorem induced_hyperbolic_charted_space_is_manifold
    (charts : E → OpenPartialHomeomorph E H2) (hcover : ∀ x : E, x ∈ (charts x).source)
    (hmetric : ∀ x : E, ∀ y ∈ (charts x).source, ∀ z ∈ (charts x).source,
      dist y z = dist (charts x y) (charts x z)) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) E := inducedHyperbolicChartedSpace charts hcover
    IsManifold (𝓡 2) ∞ E := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) E := inducedHyperbolicChartedSpace charts hcover
  apply isManifold_of_contDiffOn
  intro e d he hd
  change e ∈ Set.range (fun x => inducedEuclideanHyperbolicChart (charts x)) at he
  change d ∈ Set.range (fun x => inducedEuclideanHyperbolicChart (charts x)) at hd
  obtain ⟨x, rfl⟩ := he
  obtain ⟨y, rfl⟩ := hd
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id, Set.inter_univ] using
      euclidean_metric_chart_transition_real_smooth (charts x) (charts y) (hmetric x) (hmetric y)

end CurveComplex.Hyperbolic
