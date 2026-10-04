import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.HyperbolicLineBallSegmentCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactCanonicalDiscBoundCandidate

namespace CurveComplex.Hyperbolic
open Set

theorem regular_hexagon_side_geodesic_straightener (i : Fin 6) :
    ∃ e : H2 ≃ᵢ H2, ∀ z : H2,
      regularHexagonSideEquation i (cayley z : ℂ) = 0 ↔ (e z).re = 0 :=
  compact_disc_side_supporting_geodesic (regularHexagonSideCenter i)
    (regular_hexagon_side_center_normSq i)

theorem regular_hexagon_edge_side_equation_zero (i : Fin 6) (z : H2)
    (hz : z ∈ regularHexagonCandidate.edge i) :
    regularHexagonSideEquation i (cayley z : ℂ) = 0 := by
  obtain ⟨e, he⟩ := regular_hexagon_side_geodesic_straightener i
  have ha : (e (regularHexagonCandidate.vertex i)).re = 0 := by
    apply (he _).mp
    change regularHexagonSideEquation i (cayley (regularHexagonH2Point i) : ℂ) = 0
    rw [regularHexagonH2Point, cayley_cayleyInverse]
    exact regular_hexagon_side_equation_left_vertex i
  have hb : (e (regularHexagonCandidate.vertex (i + 1))).re = 0 := by
    apply (he _).mp
    change regularHexagonSideEquation i (cayley (regularHexagonH2Point (i + 1)) : ℂ) = 0
    rw [regularHexagonH2Point, cayley_cayleyInverse]
    exact regular_hexagon_side_equation_right_vertex i
  apply (he z).mpr
  exact ((metric_segment_iff_in_vertical_interval e
    (regularHexagonCandidate.vertex i) (regularHexagonCandidate.vertex (i + 1)) z ha hb).mp hz).1

theorem regular_hexagon_disc_radius_cosh_bound (z : H2)
    (hz : Complex.normSq (cayley z : ℂ) ≤ regularHexagonRadius ^ 2) :
    Real.cosh (dist regularHexagonCenter z) ≤ regularHexagonCoshRadius := by
  let w : Metric.ball (0 : ℂ) 1 := ⟨(cayley z : ℂ), cayley_mem_ball z⟩
  have hwpos : 0 < 1 - Complex.normSq (w : ℂ) := by
    have hn : ‖(w : ℂ)‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using w.property
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg (w : ℂ)]
  have hrpos : 0 < 1 - regularHexagonRadius ^ 2 := by
    nlinarith [regularHexagonRadius_pos, regularHexagonRadius_lt_one]
  have hd := cayleyInverse_cosh_dist
    (⟨0, by simp only [Metric.mem_ball, dist_self]; norm_num⟩) w
  change Real.cosh (dist regularHexagonCenter (cayleyInverse w)) = _ at hd
  rw [show cayleyInverse w = z from cayleyInverse_cayley z] at hd
  simp only [zero_sub, Complex.normSq_neg, Complex.normSq_zero, sub_zero, one_mul] at hd
  rw [hd]
  change 1 + 2 * Complex.normSq (w : ℂ) / (1 - Complex.normSq (w : ℂ)) ≤
    1 + 2 * regularHexagonRadius ^ 2 / (1 - regularHexagonRadius ^ 2)
  have hdiv : Complex.normSq (w : ℂ) / (1 - Complex.normSq (w : ℂ)) ≤
      regularHexagonRadius ^ 2 / (1 - regularHexagonRadius ^ 2) := by
    apply (div_le_div_iff₀ hwpos hrpos).mpr
    change Complex.normSq (w : ℂ) ≤ _ at hz
    nlinarith
  simpa only [mul_div_assoc, add_comm] using add_le_add_left (mul_le_mul_of_nonneg_left hdiv (by norm_num : (0 : ℝ) ≤ 2)) 1

set_option maxHeartbeats 1000000 in
theorem regular_hexagon_side_geodesic_radial_cut (i : Fin 6) :
    {z : H2 | regularHexagonSideEquation i (cayley z : ℂ) = 0 ∧
      Complex.normSq (cayley z : ℂ) ≤ regularHexagonRadius ^ 2} =
      regularHexagonCandidate.edge i := by
  ext z; constructor
  · rintro ⟨hs, hr⟩
    obtain ⟨e, he⟩ := regular_hexagon_side_geodesic_straightener i
    have ha : (e (regularHexagonCandidate.vertex i)).re = 0 :=
      (he _).mp (regular_hexagon_edge_side_equation_zero i _ (regularHexagonCandidate.left_mem_edge i))
    have hb : (e (regularHexagonCandidate.vertex (i + 1))).re = 0 :=
      (he _).mp (regular_hexagon_edge_side_equation_zero i _ (regularHexagonCandidate.right_mem_edge i))
    have hz : (e z).re = 0 := (he z).mp hs
    have hne : e (regularHexagonCandidate.vertex i) ≠ e (regularHexagonCandidate.vertex (i + 1)) :=
      e.injective.ne (regularHexagonCandidate.injective.ne (by fin_cases i <;> decide))
    have hEq : Real.cosh (dist (e regularHexagonCenter) (e (regularHexagonCandidate.vertex i))) =
        Real.cosh (dist (e regularHexagonCenter) (e (regularHexagonCandidate.vertex (i + 1)))) := by
      rw [e.dist_eq, e.dist_eq, regularHexagon_center_cosh_vertex, regularHexagon_center_cosh_vertex]
    have hLe : Real.cosh (dist (e regularHexagonCenter) (e z)) ≤
        Real.cosh (dist (e regularHexagonCenter) (e (regularHexagonCandidate.vertex i))) := by
      rw [e.dist_eq, e.dist_eq, regularHexagon_center_cosh_vertex]
      exact regular_hexagon_disc_radius_cosh_bound z hr
    have h := vertical_geodesic_equal_radius_ball_segment (e regularHexagonCenter)
      (e (regularHexagonCandidate.vertex i)) (e (regularHexagonCandidate.vertex (i + 1)))
      (e z) hne ha hb hz hEq hLe
    simpa only [e.dist_eq, Hexagon.edge, mem_ofPred_eq] using h
  · intro hz
    refine ⟨regular_hexagon_edge_side_equation_zero i z hz, ?_⟩
    apply regular_hexagon_closed_region_disc_bound z
    apply frontier_subset_closure
    rw [regularHexagonRegion.boundary_is_edges]
    exact mem_iUnion.mpr ⟨i, hz⟩

end CurveComplex.Hyperbolic
