import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactCanonicalPositiveQuarter
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactVertexReflectionCrossings
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactDoubleCrossDistance

namespace CurveComplex.Hyperbolic
open Set Topology

theorem regularHexagon_actual_vertex_cross_metric (i : Fin 6) :
    ∃ e : H2 ≃ᵢ H2, (e (regularHexagonCandidate.vertex i)).re = 0 ∧
      (e (regularHexagonCandidate.vertex i)).im = 1 ∧ ∃ ε : ℝ, 0 < ε ∧
      (∀ z ∈ Metric.ball (regularHexagonCandidate.vertex i) ε,
        z ∈ closure regularHexagonRegion.interior ↔
          0 ≤ (e z).re ∧ (e z).re ^ 2 + (e z).im ^ 2 ≤ 1) ∧
      ∀ a b : ClosedPolygon regularHexagonRegion,
        (a : H2) ∈ Metric.ball (regularHexagonCandidate.vertex i) (ε / 4) →
        (b : H2) ∈ Metric.ball (regularHexagonCandidate.vertex i) (ε / 4) →
        dist (Metric.toGlueL (boundaryInclusion_isometry regularHexagonRegion)
          (boundaryInclusion_isometry regularHexagonRegion) a)
          (Metric.toGlueR (boundaryInclusion_isometry regularHexagonRegion)
            (boundaryInclusion_isometry regularHexagonRegion) b) =
        min (dist (e (a : H2)) (verticalReflectionEquiv (e (b : H2))))
          (dist (e (a : H2)) (unitCircleReflectionEquiv (e (b : H2)))) := by
  obtain ⟨e, hxe, hxi, ε, he, hclosed, hinside, hfront⟩ :=
    regularHexagon_actual_positive_vertex_quarter i
  let R := regularHexagonRegion
  let x := regularHexagonCandidate.vertex i
  have hxf : x ∈ frontier R.interior := by
    rw [R.boundary_is_edges]
    exact Set.mem_iUnion.mpr ⟨i, by simp [Hexagon.edge, x]⟩
  let c : PolygonBoundary R := ⟨⟨x, frontier_subset_closure hxf⟩, hxf⟩
  refine ⟨e, hxe, hxi, ε, he, hclosed, ?_⟩
  intro a b ha hb
  have har : dist (a : H2) x < ε / 4 := Metric.mem_ball.mp ha
  have hbr : dist (b : H2) x < ε / 4 := Metric.mem_ball.mp hb
  have hal : (a : H2) ∈ Metric.ball x ε := Metric.mem_ball.mpr (by linarith)
  have hbl : (b : H2) ∈ Metric.ball x ε := Metric.mem_ball.mpr (by linarith)
  have hap := (hclosed (a : H2) hal).mp a.property
  have hbp := (hclosed (b : H2) hbl).mp b.property
  obtain ⟨p, hp⟩ := polygon_double_cross_distance_attained R a b
  have hle := polygon_double_cross_distance_le_boundary R a b c
  have hupper : dist a (boundaryInclusion R p) + dist b (boundaryInclusion R p) < ε / 2 := by
    rw [hp] at hle
    change _ ≤ dist (a : H2) x + dist (b : H2) x at hle
    linarith
  have hpball : (boundaryInclusion R p : H2) ∈ Metric.ball x ε := by
    apply Metric.mem_ball.mpr
    by_contra hn
    have hge : ε ≤ dist (boundaryInclusion R p : H2) x := le_of_not_gt hn
    have ht := dist_triangle (boundaryInclusion R p : H2) (a : H2) x
    change dist (a : H2) (boundaryInclusion R p : H2) +
      dist (b : H2) (boundaryInclusion R p : H2) < ε / 2 at hupper
    rw [dist_comm (boundaryInclusion R p : H2) (a : H2)] at ht
    nlinarith [dist_nonneg (x := (b : H2)) (y := (boundaryInclusion R p : H2))]
  have hpaxes := ((hfront _ hpball).mp p.property).2.2
  have hupperReflection (r : H2 ≃ᵢ H2) (q : H2)
      (hqball : q ∈ Metric.ball (e x) (ε / 4))
      (hqfront : 0 ≤ q.re ∧ q.re ^ 2 + q.im ^ 2 ≤ 1 ∧ (q.re = 0 ∨ q.re ^ 2 + q.im ^ 2 = 1))
      (hqdist : dist (e (a : H2)) q + dist (e (b : H2)) q = dist (e (a : H2)) (r (e (b : H2)))) :
      dist (Metric.toGlueL (boundaryInclusion_isometry R) (boundaryInclusion_isometry R) a)
        (Metric.toGlueR (boundaryInclusion_isometry R) (boundaryInclusion_isometry R) b) ≤
      dist (e (a : H2)) (r (e (b : H2))) := by
    let z := e.symm q
    have hzball : z ∈ Metric.ball x (ε / 4) := by
      change dist (e.symm q) x < ε / 4
      rw [← e.dist_eq (e.symm q) x, e.apply_symm_apply]
      exact hqball
    have hzl : z ∈ Metric.ball x ε := Metric.mem_ball.mpr
      (by have := Metric.mem_ball.mp hzball; linarith)
    have hzf : z ∈ frontier R.interior := (hfront z hzl).mpr
      (by simpa only [z, e.apply_symm_apply] using hqfront)
    let v : PolygonBoundary R := ⟨⟨z, frontier_subset_closure hzf⟩, hzf⟩
    have hv := polygon_double_cross_distance_le_boundary R a b v
    have hvdist : dist a (boundaryInclusion R v) + dist b (boundaryInclusion R v) =
        dist (e (a : H2)) (r (e (b : H2))) := by
      change dist (a : H2) z + dist (b : H2) z = _
      rw [← e.dist_eq (a : H2) z, ← e.dist_eq (b : H2) z]
      simpa only [z, e.apply_symm_apply] using hqdist
    rwa [hvdist] at hv
  have htriangleReflection (r : H2 ≃ᵢ H2) (hpfix : r (e (boundaryInclusion R p : H2)) =
      e (boundaryInclusion R p : H2)) :
      dist (e (a : H2)) (r (e (b : H2))) ≤
        dist a (boundaryInclusion R p) + dist b (boundaryInclusion R p) := by
    have ht := dist_triangle (e (a : H2)) (e (boundaryInclusion R p : H2)) (r (e (b : H2)))
    have hd : dist (e (boundaryInclusion R p : H2)) (r (e (b : H2))) =
        dist (e (b : H2)) (e (boundaryInclusion R p : H2)) := by
      calc
        _ = dist (r (e (boundaryInclusion R p : H2))) (r (e (b : H2))) :=
          congrArg (fun t => dist t (r (e (b : H2)))) hpfix.symm
        _ = dist (e (boundaryInclusion R p : H2)) (e (b : H2)) := r.dist_eq _ _
        _ = dist (e (b : H2)) (e (boundaryInclusion R p : H2)) := dist_comm _ _
    rw [hd, e.dist_eq, e.dist_eq] at ht
    exact ht
  apply le_antisymm
  · apply le_min
    · obtain ⟨q, hqball, hqzero, hqnorm, hqdist⟩ :=
        reflected_vertical_crossing_in_inner_quarter_ball (e x) (e (a : H2)) (e (b : H2))
          hxe hap.1 hbp.1 hap.2 hbp.2
          (by simpa only [Metric.mem_ball, e.dist_eq] using ha)
          (by simpa only [Metric.mem_ball, e.dist_eq] using hb)
      exact hupperReflection verticalReflectionEquiv q hqball
        ⟨hqzero.ge, hqnorm, Or.inl hqzero⟩ hqdist
    · obtain ⟨q, hqball, hqreal, hqnorm, hqdist⟩ :=
        reflected_unit_circle_crossing_in_inner_quarter_ball (e x) (e (a : H2)) (e (b : H2))
          (by rw [hxe, hxi]; norm_num) hap.1 hbp.1 hap.2 hbp.2
          (by simpa only [Metric.mem_ball, e.dist_eq] using ha)
          (by simpa only [Metric.mem_ball, e.dist_eq] using hb)
      exact hupperReflection unitCircleReflectionEquiv q hqball
        ⟨hqreal, hqnorm.le, Or.inr hqnorm⟩ hqdist
  · rw [hp]
    rcases hpaxes with hv | hn
    · exact (min_le_left _ _).trans (htriangleReflection verticalReflectionEquiv
        ((verticalReflection_fixed_iff _).mpr hv))
    · exact (min_le_right _ _).trans (htriangleReflection unitCircleReflectionEquiv
        ((unitCircleReflection_fixed_iff _).mpr hn))

end CurveComplex.Hyperbolic
