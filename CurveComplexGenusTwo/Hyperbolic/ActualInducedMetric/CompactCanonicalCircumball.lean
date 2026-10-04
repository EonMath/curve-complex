import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactPolygonMaximumPrinciple
import CurveComplexGenusTwo.Hyperbolic.CompactHexagonRegion

namespace CurveComplex.Hyperbolic
open Set Topology

noncomputable def regularHexagonCenter : H2 :=
  cayleyInverse ⟨0, by simp only [Metric.mem_ball, dist_self]; norm_num⟩

noncomputable def regularHexagonCoshRadius : ℝ :=
  1 + 2 * regularHexagonRadius ^ 2 / (1 - regularHexagonRadius ^ 2)

theorem regularHexagon_center_cosh_vertex (i : Fin 6) :
    Real.cosh (dist regularHexagonCenter (regularHexagonCandidate.vertex i)) =
      regularHexagonCoshRadius := by
  have h := cayleyInverse_cosh_dist
    (⟨0, by simp only [Metric.mem_ball, dist_self]; norm_num⟩)
    (⟨regularHexagonDiscPoint i, regularHexagonDiscPoint_mem_ball i⟩)
  change Real.cosh (dist regularHexagonCenter (regularHexagonCandidate.vertex i)) = _ at h
  rw [h]
  have hn : Complex.normSq (regularHexagonDiscPoint i) = regularHexagonRadius ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, regularHexagonDiscPoint_norm]
  simp only [zero_sub, Complex.normSq_neg, Complex.normSq_zero, sub_zero, one_mul, hn]
  rfl

theorem regularHexagon_closed_region_circumball :
    ∀ z ∈ closure regularHexagonRegion.interior,
      Real.cosh (dist regularHexagonCenter z) ≤ regularHexagonCoshRadius := by
  apply regularHexagonRegion.cosh_distance_vertex_bound
  intro i
  exact (regularHexagon_center_cosh_vertex i).le

end CurveComplex.Hyperbolic
