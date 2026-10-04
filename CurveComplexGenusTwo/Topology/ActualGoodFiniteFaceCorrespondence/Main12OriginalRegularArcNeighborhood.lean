import CurveComplexGenusTwo.Topology.Smoothing.SphereAtlasProof
import CurveComplexGenusTwo.Topology.ActualMain14CNext.Providers.Main14ActualNonloopNeighborhoodAnnulus
import CurveComplexGenusTwo.Topology.IntersectionParity.DiskFrontierStatement
import CurveComplexGenusTwo.Dictionary.Circle24.DiscBoundaryLoop

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
open scoped Manifold ContDiff
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S] [ChartedSpace Plane E]
set_option maxHeartbeats 4000000

/-- The original arbitrary nonloop arc produces its actual regular neighborhood,
INCLUDING the exact disk/core pair and actual parametrized boundary. -/
theorem actual_nonloop_regular_arc_neighborhood (M : HyperellipticModel E S)
    (a : NonLoopArc M) :
    ∃ N : ArcNeighborhood a, ∃ pair : Metric.closedBall (0 : Plane) 1 ≃ₜ N.closedSet,
      (fun z => (pair z : S)) '' ClassificationSchoenflies.standardArcCore = a.image := by
  classical
  let A := M.actualSphereSmoothAtlas
  letI : ChartedSpace Plane S := A.charts
  letI : IsManifold (𝓡 2) ∞ S := A.manifold
  letI : T2Space S := M.sphere.symm.t2Space
  letI : CompactSpace S := M.sphere.symm.compactSpace
  letI : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    isConnected_iff_connectedSpace.mp (isConnected_sphere (by
      rw [← Module.finrank_eq_rank]; simp) (0 : EuclideanSpace ℝ (Fin 3)) (by norm_num))
  letI : ConnectedSpace S := M.sphere.symm.surjective.connectedSpace M.sphere.symm.continuous
  letI : ClosedSurface S := {}
  obtain ⟨d,hd,hcore,hinside,hmarks⟩ := M.actual_nonloop_regular_disk_core_pair a
  obtain ⟨β,hβend,hβcoll,hβrange⟩ := CurveComplex.unit_disc_boundary_loop_exists
  let L := d.comp β
  obtain ⟨c,hc⟩ := CurveComplex.curve_of_simple_closed_lift L (congrArg d hβend)
    (fun s t he => hβcoll s t (hd.injective he))
  have hclosed : IsClosed (range d) := (isCompact_range d.continuous).isClosed
  have hfront : range L = frontier (range d) := by
    change range (d ∘ β) = _
    rw [range_comp,hβrange,hclosed.frontier_eq,
      LocalSurgery.embedded_surface_disk_interior_eq d hd]
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      refine ⟨mem_range_self z,?_⟩
      rintro ⟨w,hw,he⟩
      have he' : w = z := hd.injective he
      subst w
      have hzn : ‖z.val‖ < 1 := by simpa only [Set.mem_setOf_eq,Metric.mem_ball,dist_zero_right] using hw
      change ‖z.val‖ = 1 at hz
      linarith
    · rintro ⟨⟨z,rfl⟩,hn⟩
      have hzn : ‖z.val‖ = 1 := by
        have hle : ‖z.val‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using z.property
        apply le_antisymm hle
        by_contra h
        have hzball : z.val ∈ Metric.ball (0 : Plane) 1 := by
          simp only [Metric.mem_ball,dist_zero_right]; exact lt_of_not_ge h
        exact hn ⟨z,hzball,rfl⟩
      exact ⟨z,hzn,rfl⟩
  have hboundary : c.image = frontier (range d) := hc.trans hfront
  have hfree : Disjoint c.image (M.cover.branch : Set S) := by
    apply Set.disjoint_left.mpr
    intro x hx hxB
    have hxf : x ∈ frontier (range d) := hboundary ▸ hx
    have hxends : x ∈ ({a.val.map 0,a.val.map 1}:Set S) :=
      hmarks ▸ ⟨hclosed.frontier_subset hxf,hxB⟩
    have hxarc : x ∈ a.image := by
      have hzero : (0:Interval)=⟨0,by norm_num⟩ := by apply Subtype.ext; norm_num
      have hone : (1:Interval)=⟨1,by norm_num⟩ := by apply Subtype.ext; norm_num
      have hxpair : x ∈ a.val.image ∩ (M.cover.branch:Set S) := by
        rw [a.image_inter_branch]; simpa only [←hzero,←hone] using hxends
      exact hxpair.1
    exact Set.disjoint_left.mp disjoint_interior_frontier (hinside hxarc) hxf
  let N : ArcNeighborhood a := {
    closedSet := range d
    disk := hd.toHomeomorph
    arc_inside := hinside
    marked_inside := by
      rw [Set.inter_comm,hmarks]
      have hzero : (0:Interval)=⟨0,by norm_num⟩ := by apply Subtype.ext; norm_num
      have hone : (1:Interval)=⟨1,by norm_num⟩ := by apply Subtype.ext; norm_num
      simp only [←hzero,←hone]
    boundary := ⟨c,hfree⟩
    boundary_eq_frontier := hboundary }
  exact ⟨N,hd.toHomeomorph,hcore⟩

/-- The genuine regular pair and its exact lifted boundary annulus are produced
TOGETHER from the same original arc and the same literal neighborhood. -/
theorem actual_nonloop_regular_neighborhood_lift_boundary_annulus
    (M : HyperellipticModel E S) (a : NonLoopArc M) :
    ∃ N : ArcNeighborhood a, ∃ pair : Metric.closedBall (0 : Plane) 1 ≃ₜ N.closedSet,
      (fun z => (pair z : S)) '' ClassificationSchoenflies.standardArcCore = a.image ∧
      (SplitsMarked M N.boundary 2 4 ∨ SplitsMarked M N.boundary 4 2) ∧
      ∃ H : Circle × Interval ≃ₜ M.cover.projection ⁻¹' N.closedSet,
        Set.range (fun z : Circle => (H (z,0)).val) ∪
          Set.range (fun z : Circle => (H (z,1)).val) =
          M.cover.projection ⁻¹' N.boundary.image := by
  obtain ⟨N,pair,hpair⟩ := M.actual_nonloop_regular_arc_neighborhood a
  have htype := M.actual_arc_neighborhood_boundary_type a N
  let c : Circle24 M := ⟨N.boundary,htype⟩
  obtain ⟨H,hH⟩ := M.circle24_disk_lift_annulus_exact_fields c N.closedSet N.disk
    N.boundary_eq_frontier.symm (M.actual_arc_neighborhood_interior_marked_count a N)
  exact ⟨N,pair,hpair,htype,H,hH⟩
end CurveComplex.HyperellipticModel
