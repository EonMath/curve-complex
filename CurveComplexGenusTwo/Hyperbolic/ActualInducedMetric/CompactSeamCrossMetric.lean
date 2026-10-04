import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactSideHalfPlane
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.VerticalReflectionCrossing
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactDoubleCrossDistance
namespace CurveComplex.Hyperbolic
open Set Topology

theorem HexagonRegion.actual_side_positive_coordinates {P : Hexagon} (R : HexagonRegion P)
    (hP : P.IsEmbedded) (i : Fin 6) (x : H2) (hx : x ∈ P.edge i)
    (hxi : x ≠ P.vertex i) (hxn : x ≠ P.vertex (i + 1)) :
    ∃ e : H2 ≃ᵢ H2, (e x).re = 0 ∧ ∃ ε : ℝ, 0 < ε ∧
      (∀ z ∈ Metric.ball x ε, z ∈ frontier R.interior ↔ (e z).re = 0) ∧
      (∀ z ∈ Metric.ball x ε, z ∈ closure R.interior ↔ 0 ≤ (e z).re) := by
  obtain ⟨e, hxe, ε, he, hfront, hp | hn⟩ := R.actual_side_local_halfplane hP i x hx hxi hxn
  · exact ⟨e, hxe, ε, he, hfront, hp⟩
  · refine ⟨e.trans verticalReflectionEquiv, by simp [hxe], ε, he, ?_, ?_⟩
    · intro z hz
      simpa only [IsometryEquiv.trans_apply, verticalReflection_re, neg_eq_zero] using hfront z hz
    · intro z hz
      simpa only [IsometryEquiv.trans_apply, verticalReflection_re, neg_nonneg] using hn z hz

theorem HexagonRegion.actual_side_cross_metric {P : Hexagon} (R : HexagonRegion P)
    (hP : P.IsEmbedded) (i : Fin 6) (x : H2) (hx : x ∈ P.edge i)
    (hxi : x ≠ P.vertex i) (hxn : x ≠ P.vertex (i + 1)) :
    ∃ e : H2 ≃ᵢ H2, (e x).re = 0 ∧ ∃ ε : ℝ, 0 < ε ∧
      (∀ z ∈ Metric.ball x ε, z ∈ frontier R.interior ↔ (e z).re = 0) ∧
      (∀ z ∈ Metric.ball x ε, z ∈ closure R.interior ↔ 0 ≤ (e z).re) ∧
      ∀ a b : ClosedPolygon R, (a : H2) ∈ Metric.ball x (ε / 4) →
        (b : H2) ∈ Metric.ball x (ε / 4) →
        dist (Metric.toGlueL (boundaryInclusion_isometry R) (boundaryInclusion_isometry R) a)
          (Metric.toGlueR (boundaryInclusion_isometry R) (boundaryInclusion_isometry R) b) =
        dist (e (a : H2)) (verticalReflectionEquiv (e (b : H2))) := by
  obtain ⟨e, hxe, ε, he, hfront, hclosed⟩ := R.actual_side_positive_coordinates hP i x hx hxi hxn
  have hxf : x ∈ frontier R.interior := by
    rw [R.boundary_is_edges]
    exact Set.mem_iUnion.mpr ⟨i, hx⟩
  let c : PolygonBoundary R := ⟨⟨x, frontier_subset_closure hxf⟩, hxf⟩
  refine ⟨e, hxe, ε, he, hfront, hclosed, ?_⟩
  intro a b ha hb
  have har : dist (a : H2) x < ε / 4 := Metric.mem_ball.mp ha
  have hbr : dist (b : H2) x < ε / 4 := Metric.mem_ball.mp hb
  have hal : (a : H2) ∈ Metric.ball x ε := Metric.mem_ball.mpr (by linarith)
  have hbl : (b : H2) ∈ Metric.ball x ε := Metric.mem_ball.mpr (by linarith)
  have hap : 0 ≤ (e (a : H2)).re := (hclosed a hal).mp a.property
  have hbp : 0 ≤ (e (b : H2)).re := (hclosed b hbl).mp b.property
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
  have hpzero : (e (boundaryInclusion R p : H2)).re = 0 :=
    (hfront _ hpball).mp p.property
  have hpfix := (verticalReflection_fixed_iff _).mpr hpzero
  apply le_antisymm
  · obtain ⟨q, hqball, hqzero, hqdist⟩ := reflected_geodesic_crossing_in_ball
      (e x) (e (a : H2)) (e (b : H2)) hxe hap hbp
      (by simpa only [Metric.mem_ball, e.dist_eq] using ha)
      (by simpa only [Metric.mem_ball, e.dist_eq] using hb)
    let z := e.symm q
    have hzball : z ∈ Metric.ball x (ε / 4) := by
      change dist (e.symm q) x < ε / 4
      rw [← e.dist_eq, e.apply_symm_apply]
      exact hqball
    have hzl : z ∈ Metric.ball x ε := Metric.mem_ball.mpr
      (by have := Metric.mem_ball.mp hzball; linarith)
    have hzf : z ∈ frontier R.interior := (hfront z hzl).mpr (by simpa [z] using hqzero)
    let v : PolygonBoundary R := ⟨⟨z, frontier_subset_closure hzf⟩, hzf⟩
    have hv := polygon_double_cross_distance_le_boundary R a b v
    have hvdist : dist a (boundaryInclusion R v) + dist b (boundaryInclusion R v) =
        dist (e (a : H2)) (verticalReflectionEquiv (e (b : H2))) := by
      change dist (a : H2) z + dist (b : H2) z = _
      rw [← e.dist_eq (a : H2) z, ← e.dist_eq (b : H2) z]
      simpa [z] using hqdist
    rwa [hvdist] at hv
  · rw [hp]
    have ht := dist_triangle (e (a : H2)) (e (boundaryInclusion R p : H2))
      (verticalReflectionEquiv (e (b : H2)))
    have hd : dist (e (boundaryInclusion R p : H2)) (verticalReflectionEquiv (e (b : H2))) =
        dist (e (b : H2)) (e (boundaryInclusion R p : H2)) := by
      calc
        _ = dist (verticalReflectionEquiv (e (boundaryInclusion R p : H2)))
            (verticalReflectionEquiv (e (b : H2))) :=
          congrArg (fun t => dist t (verticalReflectionEquiv (e (b : H2)))) hpfix.symm
        _ = dist (e (boundaryInclusion R p : H2)) (e (b : H2)) := verticalReflectionEquiv.dist_eq _ _
        _ = dist (e (b : H2)) (e (boundaryInclusion R p : H2)) := dist_comm _ _
    rw [hd, e.dist_eq, e.dist_eq] at ht
    exact ht
end CurveComplex.Hyperbolic
