import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualInducedClosedMetricCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.InducedAtlasGenusCandidate

namespace CurveComplex.Hyperbolic
open Set Topology
open scoped Manifold ContDiff
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [T2Space S] [CompactSpace E] [PreconnectedSpace E]

theorem actual_compact_induced_genus_two_closed_hyperbolic_metric (oldAtlas : ChartedSpace (EuclideanSpace ℝ (Fin 2)) E)
    (hgenus : @IsGenus E _ oldAtlas 2) (q : BranchedDoubleCover E S)
    (identify : S ≃ₜ Metric.GlueSpace (boundaryInclusion_isometry regularHexagonRegion)
      (boundaryInclusion_isometry regularHexagonRegion))
    (hmatch : ∀ b : S, b ∈ q.branch ↔ identify b ∈ Set.range
      (fun i : Fin 6 => Metric.toGlueL (boundaryInclusion_isometry regularHexagonRegion)
        (boundaryInclusion_isometry regularHexagonRegion)
        ⟨regularHexagonCandidate.vertex i,
          hexagon_vertex_mem_closure regularHexagonCandidate regularHexagonRegion i⟩)) :
    ∃ atlas : ChartedSpace (EuclideanSpace ℝ (Fin 2)) E,
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) E := atlas
      IsGenus E 2 ∧ ∃ H : ClosedHyperbolicMetric E,
        (letI : MetricSpace E := H.metric; IsManifold (𝓡 2) ∞ E) ∧
        (∀ x y : E, H.metric.edist x y = developmentChainEDist (actualCompactDevelopmentFamily q identify) x y) ∧
        (letI : MetricSpace E := H.metric; Isometry q.deck) ∧
        (∀ x : E, x ∉ q.ramification → ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
          ∀ y ∈ U, ∀ z ∈ U, H.metric.edist y z =
            edist (identify (q.projection y)) (identify (q.projection z))) := by
  obtain ⟨atlas, H, hsmooth, hchain, hdeck, hpull⟩ :=
    actual_compact_induced_closed_hyperbolic_metric q identify hmatch
  refine ⟨atlas, ?_, H, hsmooth, hchain, hdeck, hpull⟩
  exact isGenus_of_induced_smooth_atlas oldAtlas atlas 2 hgenus hsmooth

end CurveComplex.Hyperbolic
