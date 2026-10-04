import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualModelInducedGenusMetricCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.MetricChartConeAngleCandidate

namespace CurveComplex.Hyperbolic
open Set Topology
open scoped Manifold ContDiff UpperHalfPlane
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [oldAtlas : ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem actual_model_induced_genus_two_closed_metric_cone_angles (M : HyperellipticModel E S) :
    let q : BranchedDoubleCover E S := M.cover
    ∃ identify : S ≃ₜ Metric.GlueSpace (boundaryInclusion_isometry regularHexagonRegion)
      (boundaryInclusion_isometry regularHexagonRegion),
      (∀ b : S, b ∈ q.branch ↔ identify b ∈ Set.range
        (fun i : Fin 6 => Metric.toGlueL (boundaryInclusion_isometry regularHexagonRegion)
          (boundaryInclusion_isometry regularHexagonRegion)
          ⟨regularHexagonCandidate.vertex i,
            hexagon_vertex_mem_closure regularHexagonCandidate regularHexagonRegion i⟩)) ∧
      ∃ atlas : ChartedSpace (EuclideanSpace ℝ (Fin 2)) E,
        letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) E := atlas
        IsGenus E 2 ∧ ∃ H : ClosedHyperbolicMetric E,
          (∀ x y : E, H.metric.edist x y =
            developmentChainEDist (actualCompactDevelopmentFamily q identify) x y) ∧
          (letI : MetricSpace E := H.metric; Isometry q.deck) ∧
          (∀ x : E, x ∉ q.ramification → ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
            ∀ y ∈ U, ∀ z ∈ U, H.metric.edist y z =
              edist (identify (q.projection y)) (identify (q.projection z))) ∧
          (∀ w ∈ q.ramification, @ConeAngleAt E H.metric w (2 * Real.pi)) := by
  let q : BranchedDoubleCover E S := M.cover
  letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
  letI : T2Space S := M.sphere.symm.t2Space
  obtain ⟨identify, hmatch, atlas, hgenus, H, hd, hdeck, hpull⟩ :=
    actual_model_induced_genus_two_closed_metric M
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) E := atlas
  refine ⟨identify, hmatch, atlas, hgenus, H, hd, hdeck, hpull, ?_⟩
  intro w hw
  obtain ⟨i, hi⟩ := (hmatch (q.projection w)).mp hw
  obtain ⟨g, _, hwg, hcenter, hgdist⟩ :=
    actual_branch_chain_pairwise_local_metric q identify w hw i hi.symm
  have hm : ∀ y ∈ g.source, ∀ z ∈ g.source, H.metric.dist y z = dist (g y) (g z) := by
    intro y hy z hz
    have he : H.metric.edist y z = edist (g y) (g z) := (hd y z).trans (hgdist y hy z hz)
    have h := congrArg ENNReal.toReal he
    simpa only [H.metric.edist_dist, edist_dist, ENNReal.toReal_ofReal dist_nonneg] using! h
  exact compatible_metric_chart_cone_angle_at H.metric H.compatible g w hwg hcenter hm

end CurveComplex.Hyperbolic
