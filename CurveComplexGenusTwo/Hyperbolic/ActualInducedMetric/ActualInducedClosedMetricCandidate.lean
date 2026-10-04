import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.InducedHyperbolicMetricChartSmoothCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ClosedHyperbolicCanonicalBridge
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualCompatibleBranchMetricCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualUnramifiedMetricChartsCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualCompatibleDeckMetricCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualCompactCompatibleMetricCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualDevelopmentDeckCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualBranchPairwiseMetricCandidate

namespace CurveComplex.Hyperbolic
open Set Topology
open scoped Manifold ContDiff
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [T2Space S] [CompactSpace E] [PreconnectedSpace E]

theorem actual_compact_induced_closed_hyperbolic_metric (q : BranchedDoubleCover E S)
    (identify : S ≃ₜ Metric.GlueSpace (boundaryInclusion_isometry regularHexagonRegion)
      (boundaryInclusion_isometry regularHexagonRegion))
    (hmatch : ∀ b : S, b ∈ q.branch ↔ identify b ∈ Set.range
      (fun i : Fin 6 => Metric.toGlueL (boundaryInclusion_isometry regularHexagonRegion)
        (boundaryInclusion_isometry regularHexagonRegion)
        ⟨regularHexagonCandidate.vertex i,
          hexagon_vertex_mem_closure regularHexagonCandidate regularHexagonRegion i⟩)) :
    ∃ atlas : ChartedSpace (EuclideanSpace ℝ (Fin 2)) E,
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) E := atlas
      ∃ H : ClosedHyperbolicMetric E,
        (letI : MetricSpace E := H.metric; IsManifold (𝓡 2) ∞ E) ∧
        (∀ x y : E, H.metric.edist x y = developmentChainEDist (actualCompactDevelopmentFamily q identify) x y) ∧
        (letI : MetricSpace E := H.metric; Isometry q.deck) ∧
        (∀ x : E, x ∉ q.ramification → ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
          ∀ y ∈ U, ∀ z ∈ U, H.metric.edist y z =
            edist (identify (q.projection y)) (identify (q.projection z))) := by
  obtain ⟨m, ht, hd, hdeck, hbranch⟩ := actual_compact_compatible_branch_metric q identify hmatch
  have hoff (x : E) (hx : x ∉ q.ramification) :
      ∃ g : OpenPartialHomeomorph E H2, x ∈ g.source ∧
        (∀ y ∈ g.source, ∀ z ∈ g.source, m.edist y z = edist (g y) (g z)) ∧
        (∀ y ∈ g.source, ∀ z ∈ g.source, m.edist y z =
          edist (identify (q.projection y)) (identify (q.projection z))) := by
    obtain ⟨g, hg, hxg, hbase⟩ := actual_compact_unramified_base_metric_charts q identify hmatch x hx
    have heq (y : E) (hy : y ∈ g.source) (z : E) (hz : z ∈ g.source) :
        m.edist y z = edist (g y) (g z) := by
      rw [hd]
      apply le_antisymm
      · exact developmentChainEDist_le_chain (by
          simpa only [add_zero] using DevelopmentChain.cons g hg hy hz (DevelopmentChain.nil z))
      · have hl := developmentChainEDist_base_lower_bound
          (fun v => identify (q.projection v)) (actualCompactDevelopmentFamily q identify)
          (by
            intro a ha u hu v hv
            obtain ⟨c, r, hr, ht, hc⟩ := ha
            simpa only [edist_dist] using ENNReal.ofReal_le_ofReal (hc u hu v hv)) y z
        simpa only [edist_dist, hbase y hy z hz] using hl
    refine ⟨g, hxg, heq, ?_⟩
    intro y hy z hz
    rw [heq y hy z hz, edist_dist, edist_dist, hbase y hy z hz]
  have hall (x : E) : ∃ g : OpenPartialHomeomorph E H2, x ∈ g.source ∧
      ∀ y ∈ g.source, ∀ z ∈ g.source, m.edist y z = edist (g y) (g z) := by
    by_cases hx : x ∈ q.ramification
    · obtain ⟨g, hxg, hc, hm⟩ := hbranch x hx
      exact ⟨g, hxg, hm⟩
    · obtain ⟨g, hxg, hm, hp⟩ := hoff x hx
      exact ⟨g, hxg, hm⟩
  classical
  cases ht
  letI : MetricSpace E := m
  choose charts hcover hmetric using hall
  have hdist : ∀ x : E, ∀ y ∈ (charts x).source, ∀ z ∈ (charts x).source,
      dist y z = dist (charts x y) (charts x z) := by
    intro x y hy z hz
    have h := congrArg ENNReal.toReal (hmetric x y hy z hz)
    simpa only [m.edist_dist, edist_dist, ENNReal.toReal_ofReal dist_nonneg] using! h
  let atlas := inducedHyperbolicChartedSpace charts hcover
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) E := atlas
  have hmanifold : IsManifold (𝓡 2) ∞ E :=
    induced_hyperbolic_charted_space_is_manifold charts hcover hdist
  have hsmooth : SmoothLocallyHyperbolic E :=
    induced_hyperbolic_charted_space_smooth_hyperbolic charts hcover hdist
  have hlocal : LocallyHyperbolicOff E ∅ := by
    intro x hx
    let g := charts x
    let f : g.source → H2 := fun y => g y
    have hf : Isometry f := by
      intro y z
      exact (hmetric x y y.property z z.property).symm
    refine ⟨g.source, g.open_source, hcover x, f, hf.isEmbedding, ?_⟩
    intro y z
    exact hf.dist_eq y z |>.symm
  let H : ClosedHyperbolicMetric E :=
    { metric := m
      compatible := rfl
      compact := inferInstance
      hyperbolic := hlocal
      smooth_hyperbolic := hsmooth }
  refine ⟨atlas, H, hmanifold, hd, hdeck, ?_⟩
  intro x hx
  obtain ⟨g, hxg, hm, hp⟩ := hoff x hx
  exact ⟨g.source, g.open_source, hxg, hp⟩

end CurveComplex.Hyperbolic
