import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualModelInducedConeMetricCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualCompatibleCoverAreaCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactPolygonDoubleAreaCandidate

namespace CurveComplex.Hyperbolic
open Set Topology MeasureTheory
open scoped Manifold ContDiff NNReal ENNReal MeasureTheory
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [oldAtlas : ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem actual_model_induced_genus_two_closed_metric_area_reduction (M : HyperellipticModel E S) :
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
          (∀ w ∈ q.ramification, @ConeAngleAt E H.metric w (2 * Real.pi)) ∧
          (@hausdorffArea E H.metric =
             4 * (μHE[2] : Measure H2) regularHexagonRegion.interior) := by
  let q : BranchedDoubleCover E S := M.cover
  letI : T2Space S := M.sphere.symm.t2Space
  obtain ⟨identify, hmatch, atlas, hg, H, hd, hdeck, hpull, hcone⟩ :=
    actual_model_induced_genus_two_closed_metric_cone_angles M
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) E := atlas
  refine ⟨identify, hmatch, atlas, hg, H, hd, hdeck, hpull, hcone, ?_⟩
  have hl : ∀ x : E, x ∉ q.ramification → ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ∀ z ∈ U, H.metric.dist y z = dist (identify (q.projection y))
        (identify (q.projection z)) := by
    intro x hx
    obtain ⟨U, hU, hxU, hdist⟩ := hpull x hx
    refine ⟨U, hU, hxU, ?_⟩
    intro y hy z hz
    have h := congrArg ENNReal.toReal (hdist y hy z hz)
    simpa only [H.metric.edist_dist, edist_dist, ENNReal.toReal_ofReal dist_nonneg] using! h
  let G := Metric.GlueSpace (boundaryInclusion_isometry regularHexagonRegion)
    (boundaryInclusion_isometry regularHexagonRegion)
  letI : CompactSpace G := polygon_double_compact regularHexagonRegion
  letI : MeasurableSpace G := borel G
  letI : BorelSpace G := ⟨rfl⟩
  have ha := actual_compatible_branched_cover_normalized_total_area H.metric H.compatible q identify hl
  rw [compact_polygon_double_normalized_area regularHexagonRegion] at ha
  convert ha using 1 <;> ring

end CurveComplex.Hyperbolic
