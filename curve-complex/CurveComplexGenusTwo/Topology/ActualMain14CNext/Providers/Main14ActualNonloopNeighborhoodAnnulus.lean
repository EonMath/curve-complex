import CurveComplexGenusTwo.Topology.ActualMain14CNext.Providers.Main14ActualArcBoundaryType
import CurveComplexGenusTwo.Dictionary.Circle24.ActualGivenDiskAnnulus
import CurveComplexGenusTwo.Dictionary.ActualCircle24Components

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S] [ChartedSpace Plane E]
set_option maxHeartbeats 4000000

/-- Count the actual endpoint marks in the literal enclosing disk interior. -/
theorem actual_arc_neighborhood_interior_marked_count (M : HyperellipticModel E S)
    (a : NonLoopArc M) (N : ArcNeighborhood a) :
    Set.ncard ((M.cover.branch : Set S) ∩ interior N.closedSet) = 2 := by
  classical
  have hzero : (0 : Interval) = ⟨0,by norm_num⟩ := by apply Subtype.ext; norm_num
  have hone : (1 : Interval) = ⟨1,by norm_num⟩ := by apply Subtype.ext; norm_num
  have he : (M.cover.branch : Set S) ∩ interior N.closedSet =
      {a.val.map 0,a.val.map 1} := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxB,hxi⟩
      have hh : x ∈ (M.cover.branch : Set S) ∩ N.closedSet := ⟨hxB,interior_subset hxi⟩
      have hh' := N.marked_inside ▸ hh
      simpa only [← hzero,← hone] using hh'
    · intro x hx
      have hx' : x ∈ a.val.image ∩ (M.cover.branch : Set S) := by
        rw [a.image_inter_branch]
        simpa only [← hzero,← hone] using hx
      exact ⟨hx'.2,N.arc_inside hx'.1⟩
  rw [he]
  have hn : a.val.map 0 ≠ a.val.map 1 := by simpa only [← hzero,← hone] using a.property
  simp [hn]

/-- Construct the actual annulus and exact lifted boundary from the original
nonloop arc alone. The midpoint/core equation is a separate obligation. -/
theorem actual_nonloop_neighborhood_lift_annulus_boundary
    (M : HyperellipticModel E S) (a : NonLoopArc M) :
    ∃ N : ArcNeighborhood a,
      (SplitsMarked M N.boundary 2 4 ∨ SplitsMarked M N.boundary 4 2) ∧
      ∃ H : Circle × Interval ≃ₜ M.cover.projection ⁻¹' N.closedSet,
        Set.range (fun z : Circle => (H (z,0)).val) ∪
          Set.range (fun z : Circle => (H (z,1)).val) =
          M.cover.projection ⁻¹' N.boundary.image := by
  classical
  obtain ⟨N⟩ := exists_arcNeighborhood_complete a
  have htype := M.actual_arc_neighborhood_boundary_type a N
  let c : Circle24 M := ⟨N.boundary,htype⟩
  obtain ⟨H,hH⟩ := M.circle24_disk_lift_annulus_exact_fields c N.closedSet N.disk
    N.boundary_eq_frontier.symm (M.actual_arc_neighborhood_interior_marked_count a N)
  exact ⟨N,htype,H,hH⟩

/-- The same actual boundary has precisely two disjoint upstairs circles,
exchanged by the original given deck involution. No component is supplied. -/
theorem actual_nonloop_neighborhood_lift_two_boundary_circles
    (M : HyperellipticModel E S) (a : NonLoopArc M) :
    ∃ N : ArcNeighborhood a, ∃ c d : Curve E,
      c.image ∪ d.image = M.cover.projection ⁻¹' N.boundary.image ∧
      Disjoint c.image d.image ∧ M.cover.deck '' c.image = d.image := by
  classical
  obtain ⟨N,htype,H,hH⟩ := M.actual_nonloop_neighborhood_lift_annulus_boundary a
  let c : Circle24 M := ⟨N.boundary,htype⟩
  obtain ⟨u,v,hu,hdisj,hdeck⟩ := M.actual_circle24_preimage_two_components c
  exact ⟨N,u,v,hu,hdisj,hdeck⟩
end CurveComplex.HyperellipticModel
