import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactActualVertexMetricDevelopmentCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualCoverLocalCharts

namespace CurveComplex.Hyperbolic
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]

theorem actual_branch_metric_base_development
    (q : BranchedDoubleCover E S)
    (identify : S ≃ₜ Metric.GlueSpace (boundaryInclusion_isometry regularHexagonRegion)
      (boundaryInclusion_isometry regularHexagonRegion))
    (x : E) (hx : x ∈ q.ramification) (i : Fin 6)
    (hposition : identify (q.projection x) = Metric.toGlueL
      (boundaryInclusion_isometry regularHexagonRegion)
      (boundaryInclusion_isometry regularHexagonRegion)
      ⟨regularHexagonCandidate.vertex i,
        hexagon_vertex_mem_closure regularHexagonCandidate regularHexagonRegion i⟩) :
    ∃ d : OpenPartialHomeomorph S HalfTurnMetricCone,
      q.projection x ∈ d.source ∧ ∃ p : H2, p.re = 0 ∧ p.im = 1 ∧
        d (q.projection x) = toHalfTurnMetricCone p ∧
        ∃ r : ℝ, 0 < r ∧ d.target = Metric.ball (toHalfTurnMetricCone p) r ∧
          (∀ y ∈ d.source, ∀ z ∈ d.source,
            dist (d y) (d z) = dist (identify y) (identify z)) := by
  obtain ⟨c, hc, e, hsource, p, hp, hi, r, hr, htarget, hcenter, hmetric⟩ :=
    regularHexagon_actual_vertex_centered_metric_development i
  have heqc : c = ⟨regularHexagonCandidate.vertex i,
      hexagon_vertex_mem_closure regularHexagonCandidate regularHexagonRegion i⟩ := Subtype.ext hc
  subst c
  let d := identify.toOpenPartialHomeomorph.trans e
  refine ⟨d, ?_, p, hp, hi, ?_, r, hr, ?_, ?_⟩
  · change q.projection x ∈ Set.univ ∩ identify ⁻¹' e.source
    refine ⟨Set.mem_univ _, ?_⟩
    change identify (q.projection x) ∈ e.source
    rw [hposition]
    exact hsource
  · change e (identify (q.projection x)) = _
    rw [hposition]
    exact hcenter
  · simpa [d] using htarget

  · intro y hy z hz
    exact hmetric (identify y) hy.2 (identify z) hz.2

end CurveComplex.Hyperbolic
