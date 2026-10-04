import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualCompactCompatibleMetricCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualDevelopmentDeckCandidate

namespace CurveComplex.Hyperbolic
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [T2Space S] [CompactSpace E] [PreconnectedSpace E]

theorem actual_compact_compatible_deck_isometric_metric (q : BranchedDoubleCover E S)
    (identify : S ≃ₜ Metric.GlueSpace (boundaryInclusion_isometry regularHexagonRegion)
      (boundaryInclusion_isometry regularHexagonRegion))
    (hmatch : ∀ b : S, b ∈ q.branch ↔ identify b ∈ Set.range
      (fun i : Fin 6 => Metric.toGlueL (boundaryInclusion_isometry regularHexagonRegion)
        (boundaryInclusion_isometry regularHexagonRegion)
        ⟨regularHexagonCandidate.vertex i,
          hexagon_vertex_mem_closure regularHexagonCandidate regularHexagonRegion i⟩)) :
    ∃ m : MetricSpace E,
      m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace E) ∧
      (∀ x y : E, m.edist x y = developmentChainEDist (actualCompactDevelopmentFamily q identify) x y) ∧
      @Isometry E E m.toPseudoMetricSpace.toPseudoEMetricSpace m.toPseudoMetricSpace.toPseudoEMetricSpace q.deck := by
  obtain ⟨m, ht, hd⟩ := actual_compact_compatible_chain_metric q identify hmatch
  refine ⟨m, ht, hd, ?_⟩
  letI : MetricSpace E := m
  intro x y
  change m.edist (q.deck x) (q.deck y) = m.edist x y
  rw [hd, hd, actual_development_chain_edist_deck]

end CurveComplex.Hyperbolic
