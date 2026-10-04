import CurveComplexGenusTwo.Topology.IntersectionParity.Subdisk
import CurveComplexGenusTwo.Dictionary.MarkedSphere
import CurveComplexGenusTwo.Topology.IntersectionParity.SurfaceDiskInterior
import CurveComplexGenusTwo.Topology.Smoothing.SphereAtlasProof

namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- The original disk chart supplies the disk; the Jordan candidate supplies
its boundary. The whole constructed subdisk stays in the original interior. -/
theorem relative_jordan_candidate_bounds_original_interior_disk
    (M : HyperellipticModel E S) (a : NonLoopArc M)
    (N : ArcNeighborhood a) (c : Curve S) (hc : c.image ⊆ interior N.closedSet) :
    ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S),
      IsEmbedding d ∧
      d '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} = c.image ∧
      range d ⊆ interior N.closedSet := by
  let : T2Space S := M.sphere.symm.t2Space
  let : CompactSpace S := M.sphere.symm.compactSpace
  let : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    Subtype.connectedSpace (isConnected_sphere
      (by simp only [← Module.finrank_eq_rank,finrank_euclideanSpace_fin]; norm_num)
      0 (by norm_num))
  let : ConnectedSpace S := M.sphere.symm.surjective.connectedSpace M.sphere.symm.continuous
  let := (actualSphereSmoothAtlas M).charts
  let := (actualSphereSmoothAtlas M).manifold
  let : ClosedSurface S := {}
  let original : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S) :=
    ⟨fun x => (N.disk x).val,continuous_subtype_val.comp N.disk.continuous⟩
  have ho : IsEmbedding original := IsEmbedding.subtypeVal.comp N.disk.isEmbedding
  have hrange : range original = N.closedSet := by
    ext x
    constructor
    · rintro ⟨t,rfl⟩
      exact (N.disk t).property
    · intro hx
      obtain ⟨t,ht⟩ := N.disk.surjective ⟨x,hx⟩
      exact ⟨t,congrArg Subtype.val ht⟩
  obtain ⟨d,hd,hboundary,hsub⟩ := CurveComplex.LocalSurgery.curve_in_embedded_disk_bounds_subdisk
    c original ho (hrange.symm ▸ hc.trans interior_subset)
  have hsubN : range d ⊆ N.closedSet := hrange ▸ hsub
  have hi : d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1} ⊆
      interior N.closedSet :=
    (CurveComplex.LocalSurgery.embedded_surface_disk_interior_isOpen d hd).subset_interior_iff.mpr
      ((image_subset_range _ _).trans hsubN)
  refine ⟨d,hd,hboundary,?_⟩
  rintro x ⟨t,rfl⟩
  have hnorm : ‖t.val‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using t.property
  rcases lt_or_eq_of_le hnorm with ht | ht
  · exact hi ⟨t,by simpa only [Set.mem_ofPred_eq,Metric.mem_ball,dist_zero_right] using ht,rfl⟩
  · apply hc
    rw [← hboundary]
    exact ⟨t,by simpa only [Set.mem_ofPred_eq,Metric.mem_sphere,dist_zero_right] using ht,rfl⟩

end CurveComplex.HyperellipticModel
