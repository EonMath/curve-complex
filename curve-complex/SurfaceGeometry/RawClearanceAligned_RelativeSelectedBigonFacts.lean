import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.ActualMarkedEmptyBigonCleanSides
import CurveComplexGenusTwo.Topology.ArcCounts.NonloopClassConversion

namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem relative_selected_bigon_excludes_other_original_endpoint
    (M : HyperellipticModel E S) (a b : NonLoopArc M)
    (B : ActualMarkedTwoSideDisk M a.toEssential b.toEssential) :
    ∀ x ∈ ({a.val.map 0,a.val.map 1}:Set S),
      x ≠ B.firstCorner → x ≠ B.secondCorner → x ∉ range B.disk := by
  intro x hx hxfirst hxsecond hxdisk
  have hxmark : x ∈ M.cover.branch := by
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · exact hx ▸ a.val.start_marked
    · exact Set.mem_singleton_iff.mp hx ▸ a.val.end_marked
  rcases Set.mem_insert_iff.mp (B.marks_are_corners x hxdisk hxmark) with hx | hx
  · exact hxfirst hx
  · exact hxsecond (Set.mem_singleton_iff.mp hx)

theorem relative_selected_bigon_open_interior_mark_free
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (B : ActualMarkedTwoSideDisk M a b) :
    Disjoint B.openInterior (M.cover.branch : Set S) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨u,hu,hux⟩ hxmark
  have hxc : x ∈ ({B.firstCorner,B.secondCorner}:Set S) :=
    B.marks_are_corners x ⟨u,hux⟩ hxmark
  have hxboundary : x ∈ B.disk ''
      {v | v.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
    rw [B.boundary_eq]
    left
    rcases Set.mem_insert_iff.mp hxc with hx | hx
    · exact ⟨0,B.first_zero.trans hx.symm⟩
    · exact ⟨1,B.first_one.trans (Set.mem_singleton_iff.mp hx).symm⟩
  obtain ⟨v,hv,hvx⟩ := hxboundary
  have huv : u = v := B.disk_embedded.injective (hux.trans hvx.symm)
  subst v
  have hu' : ‖u.val‖ < 1 := by
    simpa only [Set.mem_ofPred_eq,Metric.mem_ball,dist_zero_right] using hu
  have hv' : ‖u.val‖ = 1 := by
    simpa only [Set.mem_ofPred_eq,Metric.mem_sphere,dist_zero_right] using hv
  linarith

end CurveComplex.HyperellipticModel
