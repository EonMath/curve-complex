import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualCompactDevelopmentFamilyCoverageCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualDevelopmentChainNeighborhoodCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.DevelopmentChainUpperNeighborhoodCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.DevelopmentChainFiniteCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualDevelopmentChainSeparationCandidate

namespace CurveComplex.Hyperbolic
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [T2Space S] [CompactSpace E] [PreconnectedSpace E]

theorem actual_compact_compatible_chain_metric (q : BranchedDoubleCover E S)
    (identify : S ≃ₜ Metric.GlueSpace (boundaryInclusion_isometry regularHexagonRegion)
      (boundaryInclusion_isometry regularHexagonRegion))
    (hmatch : ∀ b : S, b ∈ q.branch ↔ identify b ∈ Set.range
      (fun i : Fin 6 => Metric.toGlueL (boundaryInclusion_isometry regularHexagonRegion)
        (boundaryInclusion_isometry regularHexagonRegion)
        ⟨regularHexagonCandidate.vertex i,
          hexagon_vertex_mem_closure regularHexagonCandidate regularHexagonRegion i⟩)) :
    ∃ m : MetricSpace E,
      m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace E) ∧
      ∀ x y : E, m.edist x y = developmentChainEDist (actualCompactDevelopmentFamily q identify) x y := by
  let F := actualCompactDevelopmentFamily q identify
  have hcoverage : ∀ x : E, ∃ e ∈ F, x ∈ e.source :=
    actual_compact_development_family_coverage q identify hmatch
  have hfinite : ∀ x y : E, developmentChainEDist F x y ≠ ⊤ :=
    developmentChainEDist_finite_of_chart_coverage F hcoverage
  have hbasis (x : E) : (𝓝 x).HasBasis (fun ε : ENNReal => 0 < ε)
      (fun ε => {y | developmentChainEDist F x y < ε}) := by
    apply Filter.hasBasis_iff.mpr
    intro V
    constructor
    · intro hV
      obtain ⟨U, hUV, hU, hxU⟩ := mem_nhds_iff.mp hV
      obtain ⟨R, hR, hball⟩ := actual_development_chain_ball_inside_open_neighborhood q identify x U hU hxU
      exact ⟨ENNReal.ofReal R, ENNReal.ofReal_pos.mpr hR, hball.trans hUV⟩
    · rintro ⟨ε, hε, hball⟩
      obtain ⟨R, hRnonneg, hRpos, hRε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
      have hR : 0 < R := ENNReal.ofReal_pos.mp hRpos
      obtain ⟨e, he, hxe⟩ := hcoverage x
      obtain ⟨U, hU, hxU, hUB⟩ := development_chain_ball_contains_open_chart_neighborhood F e he x hxe R hR
      apply Filter.mem_of_superset (hU.mem_nhds hxU)
      intro y hy
      exact hball (lt_trans (hUB hy) hRε)
  let p := PseudoEMetricSpace.ofEDistOfTopology (developmentChainEDist F)
    (developmentChainEDist_self F) (developmentChainEDist_comm F) (developmentChainEDist_triangle F) hbasis
  let em : EMetricSpace E :=
    { p with
      eq_of_edist_eq_zero := by
        intro x y hxy
        by_contra hne
        exact (ne_of_gt (actualCompactDevelopmentChainEDist_positive q identify x y hne)) hxy }
  letI : EMetricSpace E := em
  let m := EMetricSpace.toMetricSpace hfinite
  exact ⟨m, rfl, fun _ _ => rfl⟩

end CurveComplex.Hyperbolic
