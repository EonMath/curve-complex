import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualCompatibleDeckMetricCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualCompactCompatibleMetricCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualDevelopmentDeckCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualBranchPairwiseMetricCandidate

namespace CurveComplex.Hyperbolic
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [T2Space S] [CompactSpace E] [PreconnectedSpace E]

theorem actual_compact_compatible_branch_metric (q : BranchedDoubleCover E S)
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
      @Isometry E E m.toPseudoMetricSpace.toPseudoEMetricSpace m.toPseudoMetricSpace.toPseudoEMetricSpace q.deck ∧
      (∀ x ∈ q.ramification, ∃ g : OpenPartialHomeomorph E H2,
        x ∈ g.source ∧ g x = normalizedConeVertex ∧
        ∀ y ∈ g.source, ∀ z ∈ g.source, m.edist y z = edist (g y) (g z)) := by
  obtain ⟨m, ht, hd, hdeck⟩ := actual_compact_compatible_deck_isometric_metric q identify hmatch
  refine ⟨m, ht, hd, hdeck, ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := (hmatch (q.projection x)).mp hx
  obtain ⟨g, hg, hxg, hcenter, hmetric⟩ :=
    actual_branch_chain_pairwise_local_metric q identify x hx i hi.symm
  refine ⟨g, hxg, hcenter, ?_⟩
  intro y hy z hz
  rw [hd, hmetric y hy z hz]

end CurveComplex.Hyperbolic
