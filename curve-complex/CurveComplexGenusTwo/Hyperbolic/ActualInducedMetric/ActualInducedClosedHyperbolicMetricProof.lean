import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualModelMetricAreaReductionCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactCanonicalPolygonAreaCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.InducedMetricPullbackReuse

namespace CurveComplex.Hyperbolic
open Set Topology MeasureTheory
open scoped Manifold ContDiff NNReal ENNReal MeasureTheory
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [originalAtlas : ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem actual_induced_closed_hyperbolic_metric
    (M : HyperellipticModel E S) :
    let q : BranchedDoubleCover E S := M.cover
    ∃ atlas : ChartedSpace (EuclideanSpace ℝ (Fin 2)) E,
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) E := atlas
      IsGenus E 2 ∧
      ∃ H : ClosedHyperbolicMetric E,
        letI : MetricSpace E := H.metric
        Isometry (q.deck : E → E) ∧
        ∃ P : Hexagon, P.IsRegularRight ∧
          ∃ R : HexagonRegion P, ∃ identify : S ≃ₜ DoubledPolygon R,
            (∀ b : S, b ∈ q.branch ↔
              identify b ∈ Set.range (doubledVertex P R)) ∧
            TopologicalLocallyPullsBack R q identify ∧
            (∀ w ∈ q.ramification, ConeAngleAt E w (2 * Real.pi)) ∧
            hausdorffArea E = ENNReal.ofReal (4 * Real.pi) := by
  let q : BranchedDoubleCover E S := M.cover
  obtain ⟨identify,hmatch,atlas,hgenus,H,hd,hdeck,hpull,hcone,ha⟩ :=
    actual_model_induced_genus_two_closed_metric_area_reduction M
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) E := atlas
  letI : MetricSpace E := H.metric
  refine ⟨atlas,hgenus,H,hdeck,regularHexagonCandidate,
    regularHexagonCandidate_isRegularRight,regularHexagonRegion,identify,hmatch,?_,hcone,?_⟩
  · intro x hx
    obtain ⟨U,hU,hxU,hdist⟩ := hpull x hx
    refine ⟨U,hU,hxU,?_⟩
    intro y hy z hz
    have h := congrArg ENNReal.toReal (hdist y hy z hz)
    simpa only [H.metric.edist_dist,edist_dist,ENNReal.toReal_ofReal dist_nonneg] using! h
  · rw [regular_hexagon_normalized_interior_area] at ha
    have h₄ : (4 : ℝ≥0∞)=ENNReal.ofReal (4 : ℝ) := by norm_num
    rw [h₄,←ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤4)] at ha
    exact ha

end CurveComplex.Hyperbolic
