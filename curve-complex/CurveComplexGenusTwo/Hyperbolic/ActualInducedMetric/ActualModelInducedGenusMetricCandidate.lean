import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualInducedGenusClosedMetricCandidate
import CurveComplexGenusTwo.Hyperbolic.CompactDoubleSphere
import CurveComplexGenusTwo.Hyperbolic.FiniteSphereConfiguration
import CurveComplexGenusTwo.Dictionary.MarkedSphere

namespace CurveComplex.Hyperbolic
open Set Topology
open scoped Manifold ContDiff
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [oldAtlas : ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem actual_model_induced_genus_two_closed_metric (M : HyperellipticModel E S) :
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
              edist (identify (q.projection y)) (identify (q.projection z))) := by
  letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
  letI : T2Space S := M.sphere.symm.t2Space
  have hi : ∃ identify : S ≃ₜ Metric.GlueSpace (boundaryInclusion_isometry regularHexagonRegion)
      (boundaryInclusion_isometry regularHexagonRegion),
      ∀ b : S, b ∈ M.cover.branch ↔ identify b ∈ Set.range
        (fun i : Fin 6 => Metric.toGlueL (boundaryInclusion_isometry regularHexagonRegion)
          (boundaryInclusion_isometry regularHexagonRegion)
          ⟨regularHexagonCandidate.vertex i,
            hexagon_vertex_mem_closure regularHexagonCandidate regularHexagonRegion i⟩) := by
    classical
    let P := regularHexagonCandidate
    let R := regularHexagonRegion
    obtain ⟨d⟩ := regularHexagon_double_is_sphere
    let e : Fin 6 ≃ M.cover.branch := (Finset.equivFinOfCardEq M.cover.branch_card).symm
    let a (i : Fin 6) := M.sphere (e i).val
    let b (i : Fin 6) := d (Metric.toGlueL (boundaryInclusion_isometry R) (boundaryInclusion_isometry R) ⟨P.vertex i, hexagon_vertex_mem_closure P R i⟩)
    have ha : Function.Injective a := M.sphere.injective.comp (Subtype.val_injective.comp e.injective)
    have hb : Function.Injective b := d.injective.comp (polygon_double_vertex_injective R)
    obtain ⟨h, hh⟩ := finite_sphere_configuration_transport a b ha hb
    let identify : S ≃ₜ Metric.GlueSpace (boundaryInclusion_isometry R) (boundaryInclusion_isometry R) := M.sphere.trans (h.trans d.symm)
    refine ⟨identify, ?_⟩
    intro x
    have he (i : Fin 6) : identify (e i).val = Metric.toGlueL (boundaryInclusion_isometry R) (boundaryInclusion_isometry R) ⟨P.vertex i, hexagon_vertex_mem_closure P R i⟩ := by
      change d.symm (h (a i)) = Metric.toGlueL (boundaryInclusion_isometry R) (boundaryInclusion_isometry R) ⟨P.vertex i, hexagon_vertex_mem_closure P R i⟩
      rw [hh]
      exact d.symm_apply_apply _
    constructor
    · intro hx
      let i := e.symm ⟨x, hx⟩
      refine ⟨i, ?_⟩
      have hi : (e i).val = x := congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
      exact (he i).symm.trans (congrArg identify hi)
    · rintro ⟨i, hi⟩
      have hx : x = (e i).val := identify.injective (hi.symm.trans (he i).symm)
      rw [hx]
      exact (e i).property
  obtain ⟨identify, hmatch⟩ := hi
  obtain ⟨atlas, hg, H, _, hd, hdeck, hpull⟩ :=
    actual_compact_induced_genus_two_closed_hyperbolic_metric oldAtlas M.genusTwo M.cover identify hmatch
  exact ⟨identify, hmatch, atlas, hg, H, hd, hdeck, hpull⟩

end CurveComplex.Hyperbolic
