import CurveComplexGenusTwo.Topology.ActualMain14RelativeCancellation.RelativeFirstContactDiskContainment
import CurveComplexGenusTwo.Topology.ActualMain14RelativeCancellation.RelativeEndpointDiskEscapeFinalEntry
import CurveComplexGenusTwo.Topology.IntersectionParity.DiskFrontierStatement
import CurveComplexGenusTwo.Topology.Smoothing.SphereAtlasProof

namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem relative_clean_first_contact_endpoint_disk_produces_marked_bigon
    (M : HyperellipticModel E S) (a b : NonLoopArc M)
    (N : ArcNeighborhood a) (hb : b.image ⊆ interior N.closedSet)
    (hends : ({a.val.map 0,a.val.map 1}:Set S) = {b.val.map 0,b.val.map 1})
    (hfinite : (ArcSurgery.crossings M a.toEssential b.toEssential).Finite)
    (hpositive : (ArcSurgery.crossings M a.toEssential b.toEssential).Nonempty)
    (C : RelativeEndpointDiskCandidate M a b N)
    (hclean : range C.firstSide ∩ b.image = {a.val.map 0,C.contact})
    (hb0 : b.val.map 0 = a.val.map 0) (hb1 : b.val.map 1 = a.val.map 1)
    (hother : a.val.map 1 ∈ C.disk ''
      {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}) :
    ∃ B : ActualMarkedTwoSideDisk M a.toEssential b.toEssential,
      range B.disk ⊆ interior N.closedSet ∧
      B.secondCorner ∈ ArcSurgery.crossings M a.toEssential b.toEssential := by
  classical
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
  have hbC : b.image ⊆ range C.disk :=
    relative_clean_first_side_endpoint_disk_contains_second_arc M a b N C hb0 hclean
      (hb1.symm ▸ hother)
  obtain ⟨d,hd0,hd1,hdim⟩ := actual_nonloop_reversed_representative M a.toEssential a.property
  have hdne : d.val.map 0 ≠ d.val.map 1 := by rw [hd0,hd1]; exact a.property.symm
  let a' : NonLoopArc M := ⟨d.val,hdne⟩
  have him : a'.image = a.image := hdim
  have hstart : a'.val.map 0 = a.val.map 1 := hd0
  have hend : a'.val.map 1 = a.val.map 0 := hd1
  let N' : ArcNeighborhood a' := {
    closedSet := N.closedSet,disk := N.disk,
    arc_inside := him.symm ▸ N.arc_inside,
    marked_inside := by
      change (M.cover.branch:Set S) ∩ N.closedSet = {a'.val.map 0,a'.val.map 1}
      rw [hstart,hend,Set.pair_comm]
      exact N.marked_inside,
    boundary := N.boundary,boundary_eq_frontier := N.boundary_eq_frontier }
  have hends' : ({a'.val.map 0,a'.val.map 1}:Set S) = {b.val.map 0,b.val.map 1} := by
    rw [hstart,hend,Set.pair_comm]
    exact hends
  have hcrossings : ArcSurgery.crossings M a'.toEssential b.toEssential =
      ArcSurgery.crossings M a.toEssential b.toEssential := by
    change (a'.image \ (M.cover.branch:Set S)) ∩ (b.image \ (M.cover.branch:Set S)) = _
    rw [him]
    rfl
  obtain ⟨F,hFclean⟩ := relative_first_contacts_produce_original_clean_endpoint_disk_candidate M a' b N' hb
    hends' (hcrossings.symm ▸ hfinite) (hcrossings.symm ▸ hpositive)
  have hFaC : range F.firstSide ⊆ range C.disk := by
    by_cases haC : a.image ⊆ range C.disk
    · exact (him ▸ F.first_on_arc).trans haC
    · obtain ⟨q,hq,hqa,hqC,hq1,hqside,hqcross,hqin⟩ :=
        relative_endpoint_disk_first_arc_escape_final_entry M a b N C hother haC
      let A : C(Interval,S) := ⟨a'.val.map,a'.val.continuous⟩
      have hA : IsEmbedding A := (A.continuous.isClosedEmbedding a'.injective).isEmbedding
      have hqa' : range q ⊆ a'.image := him.symm ▸ hqa
      obtain ⟨u,hu⟩ := hqa' (mem_range_self 0)
      have huA : A u = q 0 := hu
      have hFclean' : range F.firstSide ∩ b.image = {A 0,F.firstSide 1} := by
        rw [F.first_one]
        exact hFclean
      have hu0 : u ≠ 0 := by
        intro he
        have heq : q 0 = q 1 := hu.symm.trans
          ((congrArg a'.val.map he).trans (hstart.trans hq1.symm))
        have hz := hq.injective heq
        norm_num at hz
      have hFq : range F.firstSide ⊆ range q :=
        CurveComplex.LocalSurgery.clean_common_endpoint_prefix_subset_returning_prefix
          A F.firstSide q hA F.first_embedded F.first_on_arc hqa'
          F.first_zero ⟨1,hq1.trans hstart.symm⟩ b.image hFclean'
          u (huA.symm ▸ mem_range_self 0) (huA.symm ▸ hqcross.2.1) hu0
      exact hFq.trans hqC
  have hinter (t u : Interval) (he : F.firstSide t = F.secondSide u) :
      (t=0 ∧ u=0) ∨ (t=1 ∧ u=1) := by
    have hx : F.firstSide t ∈ ({a'.val.map 0,F.contact}:Set S) :=
      F.sides_inter ▸ (show F.firstSide t ∈ range F.firstSide ∩ range F.secondSide from
        ⟨mem_range_self t,⟨u,he.symm⟩⟩)
    rcases mem_insert_iff.mp hx with hx | hx
    · exact Or.inl ⟨F.first_embedded.injective (hx.trans F.first_zero.symm),
        F.second_embedded.injective (he.symm.trans (hx.trans F.second_zero.symm))⟩
    · have hx' := mem_singleton_iff.mp hx
      exact Or.inr ⟨F.first_embedded.injective (hx'.trans F.first_one.symm),
        F.second_embedded.injective (he.symm.trans (hx'.trans F.second_one.symm))⟩
  obtain ⟨c,hc⟩ := CurveComplex.exists_curve_of_two_arcs F.firstSide F.secondSide
    F.first_embedded.injective F.second_embedded.injective
    (F.first_zero.trans F.second_zero.symm) (F.first_one.trans F.second_one.symm) hinter
  have hcC : c.image ⊆ range C.disk := by
    rw [hc]
    exact union_subset hFaC (F.second_on_arc.trans hbC)
  obtain ⟨k,hk,hkb,hkC⟩ := CurveComplex.LocalSurgery.curve_in_embedded_disk_bounds_subdisk
    c C.disk C.disk_embedded hcC
  let G : RelativeEndpointDiskCandidate M a' b N' := {
    contact := F.contact,contact_crossing := F.contact_crossing,
    firstSide := F.firstSide,secondSide := F.secondSide,
    first_embedded := F.first_embedded,second_embedded := F.second_embedded,
    first_zero := F.first_zero,second_zero := F.second_zero,
    first_one := F.first_one,second_one := F.second_one,
    first_on_arc := F.first_on_arc,second_on_arc := F.second_on_arc,sides_inter := F.sides_inter,
    disk := k,disk_embedded := hk,boundary_eq := hkb.trans hc,
    disk_inside := hkC.trans C.disk_inside }
  have hout : a'.val.map 1 ∉ range G.disk := by
    rintro ⟨u,hu⟩
    have hnorm : ‖u.val‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall,dist_zero_right] using u.property
    have hne : ‖u.val‖ ≠ 1 := by
      intro he
      apply relative_endpoint_disk_candidate_opposite_endpoint_not_on_boundary M a' b N' G
      exact ⟨u,by simpa only [Set.mem_ofPred_eq,Metric.mem_sphere,dist_zero_right] using he,hu⟩
    have hkin : k '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1} ⊆
        C.disk '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
      rw [← CurveComplex.LocalSurgery.embedded_surface_disk_interior_eq C.disk C.disk_embedded]
      exact (CurveComplex.LocalSurgery.embedded_surface_disk_interior_isOpen k hk).subset_interior_iff.mpr
        ((image_subset_range _ _).trans hkC)
    have hxint : a.val.map 0 ∈ C.disk ''
        {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1} := hend ▸ hkin ⟨u,
      by simpa only [Set.mem_ofPred_eq,Metric.mem_ball,dist_zero_right]
        using lt_of_le_of_ne hnorm hne,hu⟩
    have hxbound : a.val.map 0 ∈ C.disk ''
        {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} :=
      C.boundary_eq.symm ▸ (show a.val.map 0 ∈ range C.firstSide ∪ range C.secondSide from
        Or.inl ⟨0,C.first_zero⟩)
    obtain ⟨v,hv,hv0⟩ := hxint
    obtain ⟨w,hw,hw0⟩ := hxbound
    have hvw := C.disk_embedded.injective (hv0.trans hw0.symm)
    subst w
    have hv' : ‖v.val‖ < 1 := by
      simpa only [Set.mem_ofPred_eq,Metric.mem_ball,dist_zero_right] using hv
    have hw' : ‖v.val‖ = 1 := by
      simpa only [Set.mem_ofPred_eq,Metric.mem_sphere,dist_zero_right] using hw
    linarith
  obtain ⟨B,hBN,hBcontact⟩ :=
    relative_endpoint_candidate_other_endpoint_outside_produces_marked_bigon M a' b N' G hout
  exact ⟨{
    firstCorner := B.firstCorner,secondCorner := B.secondCorner,
    firstSide := B.firstSide,secondSide := B.secondSide,
    first_embedded := B.first_embedded,second_embedded := B.second_embedded,
    first_zero := B.first_zero,first_one := B.first_one,
    second_zero := B.second_zero,second_one := B.second_one,
    first_on_curve := (show range B.firstSide ⊆ a.image from
      him ▸ (show range B.firstSide ⊆ a'.image from B.first_on_curve)),
    second_on_curve := B.second_on_curve,
    sides_inter := B.sides_inter,disk := B.disk,disk_embedded := B.disk_embedded,
    boundary_eq := B.boundary_eq,marks_are_corners := B.marks_are_corners },hBN,hcrossings ▸ hBcontact⟩

end CurveComplex.HyperellipticModel
