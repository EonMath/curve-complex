import CurveComplexGenusTwo.Topology.ActualMain14RelativeCancellation.RelativeCleanFirstContactMarkedBigon

namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem relative_oriented_original_initial_marked_bigon
    (M : HyperellipticModel E S) (a b : NonLoopArc M)
    (N : ArcNeighborhood a) (hb : b.image ⊆ interior N.closedSet)
    (hends : ({a.val.map 0,a.val.map 1}:Set S) = {b.val.map 0,b.val.map 1})
    (hb0 : b.val.map 0 = a.val.map 0) (hb1 : b.val.map 1 = a.val.map 1)
    (hfinite : (ArcSurgery.crossings M a.toEssential b.toEssential).Finite)
    (hpositive : (ArcSurgery.crossings M a.toEssential b.toEssential).Nonempty) :
    ∃ B : ActualMarkedTwoSideDisk M a.toEssential b.toEssential,
      range B.disk ⊆ interior N.closedSet ∧
      B.secondCorner ∈ ArcSurgery.crossings M a.toEssential b.toEssential := by
  obtain ⟨C,hclean⟩ := relative_oriented_first_contact_produces_clean_endpoint_disk_candidate
    M a b N hb hb0.symm hfinite hpositive
  by_cases hother : a.val.map 1 ∉ range C.disk
  · exact relative_endpoint_candidate_other_endpoint_outside_produces_marked_bigon M a b N C hother
  · have hother_inside : a.val.map 1 ∈ C.disk ''
        {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
      obtain ⟨u,hu⟩ := not_not.mp hother
      have hnorm : ‖u.val‖ ≤ 1 := by
        simpa only [Metric.mem_closedBall,dist_zero_right] using u.property
      have hne : ‖u.val‖ ≠ 1 := by
        intro he
        apply relative_endpoint_disk_candidate_opposite_endpoint_not_on_boundary M a b N C
        exact ⟨u,by simpa only [Set.mem_ofPred_eq,Metric.mem_sphere,dist_zero_right] using he,hu⟩
      exact ⟨u,by simpa only [Set.mem_ofPred_eq,Metric.mem_ball,dist_zero_right]
        using lt_of_le_of_ne hnorm hne,hu⟩
    exact relative_clean_first_contact_endpoint_disk_produces_marked_bigon
      M a b N hb hends hfinite hpositive C hclean hb0 hb1 hother_inside

theorem relative_original_finite_contacts_produce_initial_marked_bigon
    (M : HyperellipticModel E S) (a b : NonLoopArc M)
    (N : ArcNeighborhood a) (hb : b.image ⊆ interior N.closedSet)
    (hends : ({a.val.map 0,a.val.map 1}:Set S) = {b.val.map 0,b.val.map 1})
    (hfinite : (ArcSurgery.crossings M a.toEssential b.toEssential).Finite)
    (hpositive : (ArcSurgery.crossings M a.toEssential b.toEssential).Nonempty) :
    ∃ B : ActualMarkedTwoSideDisk M a.toEssential b.toEssential,
      range B.disk ⊆ interior N.closedSet ∧
      B.secondCorner ∈ ArcSurgery.crossings M a.toEssential b.toEssential := by
  have ha0 : a.val.map 0 ∈ ({b.val.map 0,b.val.map 1}:Set S) := by
    rw [← hends]
    exact mem_insert _ _
  have ha1 : a.val.map 1 ∈ ({b.val.map 0,b.val.map 1}:Set S) := by
    rw [← hends]
    exact Or.inr (mem_singleton _)
  rcases mem_insert_iff.mp ha0 with he0 | he1
  · have he1 : a.val.map 1 = b.val.map 1 := by
      rcases mem_insert_iff.mp ha1 with h | h
      · exact False.elim (a.property (he0.trans h.symm))
      · exact mem_singleton_iff.mp h
    exact relative_oriented_original_initial_marked_bigon M a b N hb hends
      he0.symm he1.symm hfinite hpositive
  · have he0 : a.val.map 0 = b.val.map 1 := mem_singleton_iff.mp he1
    have he1 : a.val.map 1 = b.val.map 0 := by
      rcases mem_insert_iff.mp ha1 with h | h
      · exact h
      · exact False.elim (a.property (he0.trans (mem_singleton_iff.mp h).symm))
    obtain ⟨d,hd0,hd1,hdim⟩ := actual_nonloop_reversed_representative M b.toEssential b.property
    have hdne : d.val.map 0 ≠ d.val.map 1 := by rw [hd0,hd1]; exact b.property.symm
    let b' : NonLoopArc M := ⟨d.val,hdne⟩
    have him : b'.image = b.image := hdim
    have hb'0 : b'.val.map 0 = a.val.map 0 := hd0.trans he0.symm
    have hb'1 : b'.val.map 1 = a.val.map 1 := hd1.trans he1.symm
    have hends' : ({a.val.map 0,a.val.map 1}:Set S) = {b'.val.map 0,b'.val.map 1} := by
      rw [hb'0,hb'1]
    have hc : ArcSurgery.crossings M a.toEssential b'.toEssential =
        ArcSurgery.crossings M a.toEssential b.toEssential := by
      change (a.image \ (M.cover.branch:Set S)) ∩ (b'.image \ (M.cover.branch:Set S)) = _
      rw [him]
      rfl
    obtain ⟨B,hBN,hBc⟩ := relative_oriented_original_initial_marked_bigon M a b' N
      (him.symm ▸ hb) hends' hb'0 hb'1 (hc.symm ▸ hfinite) (hc.symm ▸ hpositive)
    have hBsecond : range B.secondSide ⊆ b.image :=
      him ▸ (show range B.secondSide ⊆ b'.image from B.second_on_curve)
    exact ⟨{
      firstCorner := B.firstCorner,secondCorner := B.secondCorner,
      firstSide := B.firstSide,secondSide := B.secondSide,
      first_embedded := B.first_embedded,second_embedded := B.second_embedded,
      first_zero := B.first_zero,second_zero := B.second_zero,
      first_one := B.first_one,second_one := B.second_one,
      first_on_curve := B.first_on_curve,second_on_curve := hBsecond,
      sides_inter := B.sides_inter,disk := B.disk,disk_embedded := B.disk_embedded,
      boundary_eq := B.boundary_eq,marks_are_corners := B.marks_are_corners },hBN,hc ▸ hBc⟩

end CurveComplex.HyperellipticModel
