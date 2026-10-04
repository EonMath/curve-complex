import CurveComplexGenusTwo.Topology.ActualMain14RelativeCancellation.RelativeBigonSelfIntrusionSubdisk

namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem relative_marked_bigon_either_self_intrusion_smaller_disk
    (M : HyperellipticModel E S) (a b : NonLoopArc M)
    (B : ActualMarkedTwoSideDisk M a.toEssential b.toEssential)
    (hin : ((a.image ∪ b.image) ∩ B.openInterior).Nonempty) :
    ∃ D : ActualMarkedTwoSideDisk M a.toEssential b.toEssential,
      range D.disk ⊆ range B.disk ∧
      (∃ x ∈ ({B.firstCorner,B.secondCorner}:Set S), x ∉ range D.disk) ∧
      (D.firstCorner ∈ ArcSurgery.crossings M a.toEssential b.toEssential ∨
        D.secondCorner ∈ ArcSurgery.crossings M a.toEssential b.toEssential) := by
  obtain ⟨x,hxa | hxb,hxB⟩ := hin
  · exact relative_marked_bigon_first_self_intrusion_smaller_disk M a b B ⟨x,hxa,hxB⟩
  · let swap {c d : EssentialMarkedArc M} (K : ActualMarkedTwoSideDisk M c d) :
        ActualMarkedTwoSideDisk M d c := {
      firstCorner := K.firstCorner,secondCorner := K.secondCorner,
      firstSide := K.secondSide,secondSide := K.firstSide,
      first_embedded := K.second_embedded,second_embedded := K.first_embedded,
      first_zero := K.second_zero,first_one := K.second_one,
      second_zero := K.first_zero,second_one := K.first_one,
      first_on_curve := K.second_on_curve,second_on_curve := K.first_on_curve,
      sides_inter := by rw [Set.inter_comm,K.sides_inter],
      disk := K.disk,disk_embedded := K.disk_embedded,
      boundary_eq := K.boundary_eq.trans (Set.union_comm _ _),
      marks_are_corners := K.marks_are_corners }
    obtain ⟨D,hsub,hmissing,hcontact⟩ :=
      relative_marked_bigon_first_self_intrusion_smaller_disk M b a (swap B) ⟨x,hxb,hxB⟩
    refine ⟨swap D,hsub,hmissing,?_⟩
    simpa only [ArcSurgery.crossings,Set.inter_comm] using hcontact

theorem relative_initial_marked_disk_produces_confined_empty_bigon
    (M : HyperellipticModel E S) (a b : NonLoopArc M)
    (N : ArcNeighborhood a)
    (hfinite : (ArcSurgery.crossings M a.toEssential b.toEssential).Finite)
    (B : ActualMarkedTwoSideDisk M a.toEssential b.toEssential)
    (hBN : range B.disk ⊆ interior N.closedSet)
    (hcontact : B.firstCorner ∈ ArcSurgery.crossings M a.toEssential b.toEssential ∨
      B.secondCorner ∈ ArcSurgery.crossings M a.toEssential b.toEssential) :
    ∃ D : ActualMarkedTwoSideDisk M a.toEssential b.toEssential,
      range D.disk ⊆ interior N.closedSet ∧
      Disjoint D.openInterior (a.image ∪ b.image ∪ (M.cover.branch : Set S)) ∧
      (D.firstCorner ∈ ArcSurgery.crossings M a.toEssential b.toEssential ∨
        D.secondCorner ∈ ArcSurgery.crossings M a.toEssential b.toEssential) ∧
      (∀ x ∈ ({a.val.map 0,a.val.map 1}:Set S),
        x ≠ D.firstCorner → x ≠ D.secondCorner → x ∉ range D.disk) := by
  classical
  let C : Set S := a.image ∩ b.image
  have hCf : C.Finite :=
    (hfinite.union (Set.toFinite ({a.val.map 0,a.val.map 1}:Set S))).subset (by
      intro x hx
      by_cases hxmark : x ∈ M.cover.branch
      · right
        obtain ⟨t,ht⟩ := hx.1
        rcases a.val.marked_only_at_ends t (ht ▸ hxmark) with ht0 | ht1
        · exact Or.inl ((congrArg a.val.map ht0).symm.trans ht).symm
        · exact Or.inr ((congrArg a.val.map ht1).symm.trans ht).symm
      · exact Or.inl ⟨⟨hx.1,hxmark⟩,hx.2,hxmark⟩)
  let energy (D : ActualMarkedTwoSideDisk M a.toEssential b.toEssential) : ℕ :=
    (C ∩ range D.disk).ncard
  let P : ℕ → Prop := fun n =>
    ∃ D : ActualMarkedTwoSideDisk M a.toEssential b.toEssential,
      range D.disk ⊆ range B.disk ∧
      (D.firstCorner ∈ ArcSurgery.crossings M a.toEssential b.toEssential ∨
        D.secondCorner ∈ ArcSurgery.crossings M a.toEssential b.toEssential) ∧ energy D = n
  have hex : ∃ n,P n := ⟨energy B,B,Subset.rfl,hcontact,rfl⟩
  obtain ⟨D,hDB,hDcontact,hDenergy⟩ := Nat.find_spec hex
  have hempty : Disjoint D.openInterior (a.image ∪ b.image) := by
    apply Set.disjoint_left.mpr
    intro x hxDisk hxArc
    obtain ⟨F,hFD,⟨z,hzcorner,hznotF⟩,hFcontact⟩ :=
      relative_marked_bigon_either_self_intrusion_smaller_disk M a b D ⟨x,hxArc,hxDisk⟩
    have hzC : z ∈ C := by
      rcases mem_insert_iff.mp hzcorner with hz | hz
      · exact ⟨D.first_on_curve ⟨0,D.first_zero.trans hz.symm⟩,
          D.second_on_curve ⟨0,D.second_zero.trans hz.symm⟩⟩
      · have hz' := mem_singleton_iff.mp hz
        exact ⟨D.first_on_curve ⟨1,D.first_one.trans hz'.symm⟩,
          D.second_on_curve ⟨1,D.second_one.trans hz'.symm⟩⟩
    have hzD : z ∈ range D.disk := image_subset_range _ _ (D.boundary_eq.symm ▸
      (show z ∈ range D.firstSide ∪ range D.secondSide from
        Or.inl (by
          rcases mem_insert_iff.mp hzcorner with hz | hz
          · exact ⟨0,D.first_zero.trans hz.symm⟩
          · exact ⟨1,D.first_one.trans (mem_singleton_iff.mp hz).symm⟩)))
    have hlt : energy F < energy D := Set.ncard_lt_ncard
      (Set.ssubset_iff_subset_ne.mpr ⟨Set.inter_subset_inter_right C hFD,by
        intro he
        have hzF : z ∈ C ∩ range F.disk := he.symm ▸ (show z ∈ C ∩ range D.disk from ⟨hzC,hzD⟩)
        exact hznotF hzF.2⟩) (hCf.inter_of_left _)
    exact Nat.find_min hex (hlt.trans_eq hDenergy)
      ⟨F,hFD.trans hDB,hFcontact,rfl⟩
  exact ⟨D,hDB.trans hBN,
    hempty.union_right (relative_selected_bigon_open_interior_mark_free M _ _ D),
    hDcontact,relative_selected_bigon_excludes_other_original_endpoint M a b D⟩

end CurveComplex.HyperellipticModel
