import CurveComplexGenusTwo.Topology.Smoothing.FiniteStarSeed
open Set Schoenflies Bornology

-- A bounded connected open geometric sector with this boundary is the
-- actual Jordan inside, rather than an assumed disk chart.
theorem bounded_jordan_frontier_region_eq_inside {C U : Set Plane} (hC : IsJordanCurve C)
    (hU : IsOpen U) (hconn : IsConnected U) (hbounded : IsBounded U)
    (hfront : frontier U = C) : U = inside C := by
  obtain ⟨x,hx⟩ := hconn.nonempty
  have hUC : U ⊆ Cᶜ := by
    intro y hy
    rw [← hfront, hU.frontier_eq]
    exact fun he => he.2 hy
  have hcomp : connectedComponentIn Cᶜ x = U := by
    apply Plane.connectedComponentIn_eq_of_frontier_disjoint hU hconn.isPreconnected hUC
    · rw [hfront]
      exact inter_compl_self C
    · exact hx
  have hxin : x ∈ inside C := ⟨hUC hx, hcomp.symm ▸ hbounded⟩
  exact hcomp.symm.trans ((jordan_curve_theorem hC).connectedComponentIn_eq_inside hxin)

#print axioms bounded_jordan_frontier_region_eq_inside
