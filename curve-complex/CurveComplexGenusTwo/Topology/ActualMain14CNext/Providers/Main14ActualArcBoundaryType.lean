import CurveComplexGenusTwo.Topology.ActualMain14CNext.Providers.Main14ActualNonloopRegularPair
import CurveComplexGenusTwo.Dictionary.PuncturedCircleClosedSides
import CurveComplexGenusTwo.Intersection.ExistsArcNeighborhoodCandidate

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S] [ChartedSpace Plane E]
set_option maxHeartbeats 4000000

/-- The literal boundary of any actual two-endpoint disk enclosure is 2|4.
No marked side or Circle24 classification is supplied. -/
theorem actual_arc_neighborhood_boundary_type (M : HyperellipticModel E S)
    (a : NonLoopArc M) (N : ArcNeighborhood a) :
    SplitsMarked M N.boundary 2 4 ∨ SplitsMarked M N.boundary 4 2 := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  have hzero : (0 : Interval) = ⟨0,by norm_num⟩ := by apply Subtype.ext; norm_num
  have hone : (1 : Interval) = ⟨1,by norm_num⟩ := by apply Subtype.ext; norm_num
  have hKcompact : IsCompact N.closedSet := by
    have h := isCompact_range N.disk.continuous
    have hr : range (fun z => (N.disk z : S)) = N.closedSet := by
      ext x; constructor
      · rintro ⟨z,rfl⟩; exact (N.disk z).property
      · intro hx; exact ⟨N.disk.symm ⟨x,hx⟩,congrArg Subtype.val (N.disk.apply_symm_apply ⟨x,hx⟩)⟩
    rw [← hr]
    exact isCompact_range (continuous_subtype_val.comp N.disk.continuous)
  have hKclosed := hKcompact.isClosed
  obtain ⟨U,V,hU,hV,hUc,hVc,hUV,hcover,dU,dV,hUb,hVb,hUi,hVi,hclU,hclV⟩ :=
    M.puncturedCircle_closedSides N.boundary
  have hpart (W : Set S) (hW : IsConnected W) (hWc : W ⊆ N.boundary.imageᶜ) :
      W ⊆ interior N.closedSet ∨ W ⊆ N.closedSetᶜ := by
    apply hW.isPreconnected.subset_or_subset isOpen_interior hKclosed.isOpen_compl
      (Set.disjoint_left.mpr (fun _ hi ho => ho (interior_subset hi)))
    intro x hx
    by_cases hxK : x ∈ N.closedSet
    · left
      by_contra hxi
      have hxf : x ∈ frontier N.closedSet := (mem_frontier_iff_notMem_interior hxK).mpr hxi
      exact hWc hx (N.boundary_eq_frontier.symm ▸ hxf)
    · exact Or.inr hxK
  have hUcomp : U ⊆ N.boundary.imageᶜ := by rw [← hcover]; exact subset_union_left
  have hVcomp : V ⊆ N.boundary.imageᶜ := by rw [← hcover]; exact subset_union_right
  have hstart : a.val.map 0 ∈ interior N.closedSet := N.arc_inside (mem_range_self 0)
  have hstartc : a.val.map 0 ∉ N.boundary.image := by
    rw [N.boundary_eq_frontier]
    exact Set.disjoint_left.mp disjoint_interior_frontier hstart
  have houtside : ∃ x, x ∈ M.cover.branch ∧ x ∉ N.closedSet := by
    let F : Finset S := {a.val.map 0,a.val.map 1}
    have hF : F.card < M.cover.branch.card := by
      rw [M.cover.branch_card]
      have hh := Finset.card_insert_le (a.val.map 0) ({a.val.map 1}:Finset S)
      simp only [Finset.card_singleton] at hh
      change ({a.val.map 0,a.val.map 1}:Finset S).card < 6
      omega
    obtain ⟨x,hx,hxn⟩ := Finset.exists_mem_notMem_of_card_lt_card hF
    refine ⟨x,hx,?_⟩
    intro hxK
    have he : x ∈ ({a.val.map 0,a.val.map 1}:Set S) := by
      have hh : x ∈ (M.cover.branch:Set S) ∩ N.closedSet := ⟨hx,hxK⟩
      have hh' := N.marked_inside ▸ hh
      convert hh' using 1
    exact hxn (by simpa [F] using he)
  have hmake (W Z : Set S) (hWo : IsOpen W) (hZo : IsOpen Z)
      (hWc : IsConnected W) (hZc : IsConnected Z) (hWZ : Disjoint W Z)
      (hWZcover : W ∪ Z = N.boundary.imageᶜ)
      (hWin : W ⊆ interior N.closedSet) (hZout : Z ⊆ N.closedSetᶜ) :
      SplitsMarked M N.boundary 2 4 := by
    have hWint : W = interior N.closedSet := by
      apply Set.Subset.antisymm hWin
      intro x hx
      have hxc : x ∉ N.boundary.image := by
        rw [N.boundary_eq_frontier]
        exact Set.disjoint_left.mp disjoint_interior_frontier hx
      rcases (show x ∈ W ∪ Z from by rw [hWZcover]; exact hxc) with hw | hz
      · exact hw
      · exact False.elim (hZout hz (interior_subset hx))
    have hfilter : M.cover.branch.filter (· ∈ W) = {a.val.map 0,a.val.map 1} := by
      ext x
      simp only [Finset.mem_filter,Finset.mem_insert,Finset.mem_singleton]
      constructor
      · rintro ⟨hxB,hxW⟩
        have hh : x ∈ (M.cover.branch:Set S) ∩ N.closedSet :=
          ⟨hxB,interior_subset (hWin hxW)⟩
        have hh' := N.marked_inside ▸ hh
        simpa only [← hzero,← hone,Set.mem_insert_iff,Set.mem_singleton_iff] using hh'
      · intro hx
        have hxarc : x ∈ a.val.image ∩ (M.cover.branch:Set S) := by
          rw [a.image_inter_branch]; simpa only [← hzero,← hone,Set.mem_insert_iff,Set.mem_singleton_iff] using hx
        exact ⟨hxarc.2,hWint.symm ▸ N.arc_inside hxarc.1⟩
    have htwo : (M.cover.branch.filter (· ∈ W)).card = 2 := by
      rw [hfilter]
      have hneq : a.val.map 0 ≠ a.val.map 1 := by convert a.property using 1
      simp [hneq]
    have hsum : (M.cover.branch.filter (· ∈ W)).card +
        (M.cover.branch.filter (· ∈ Z)).card = 6 := by
      have hd : Disjoint (M.cover.branch.filter (· ∈ W)) (M.cover.branch.filter (· ∈ Z)) := by
        apply Finset.disjoint_left.mpr
        intro x hx hy
        exact Set.disjoint_left.mp hWZ (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
      have hu : M.cover.branch.filter (· ∈ W) ∪ M.cover.branch.filter (· ∈ Z) = M.cover.branch := by
        ext x
        simp only [Finset.mem_union,Finset.mem_filter]
        constructor
        · rintro (⟨hx,_⟩ | ⟨hx,_⟩) <;> exact hx
        · intro hx
          have hxc : x ∉ N.boundary.image := fun hc =>
            Set.disjoint_left.mp N.boundary.avoids_branch hc hx
          rcases (show x ∈ W ∪ Z from by rw [hWZcover]; exact hxc) with hw | hz
          · exact Or.inl ⟨hx,hw⟩
          · exact Or.inr ⟨hx,hz⟩
      rw [← Finset.card_union_of_disjoint hd,hu,M.cover.branch_card]
    exact ⟨W,Z,hWo,hZo,hWc,hZc,hWc.nonempty,hZc.nonempty,hWZ,hWZcover,htwo,by omega⟩
  rcases hpart U hUc hUcomp with hUin | hUout <;>
    rcases hpart V hVc hVcomp with hVin | hVout
  · obtain ⟨x,hxB,hxK⟩ := houtside
    have hxc : x ∉ N.boundary.image := fun hc => hxK (hKclosed.frontier_subset (N.boundary_eq_frontier ▸ hc))
    rcases (show x ∈ U ∪ V from by rw [hcover]; exact hxc) with hu | hv
    · exact False.elim (hxK (interior_subset (hUin hu)))
    · exact False.elim (hxK (interior_subset (hVin hv)))
  · exact Or.inl (hmake U V hU hV hUc hVc hUV hcover hUin hVout)
  · have h := hmake V U hV hU hVc hUc hUV.symm ((union_comm V U).trans hcover) hVin hUout
    obtain ⟨W,Z,hWo,hZo,hWc,hZc,hWn,hZn,hWZ,hcov,h2,h4⟩ := h
    exact Or.inr ⟨Z,W,hZo,hWo,hZc,hWc,hZn,hWn,hWZ.symm,(union_comm Z W).trans hcov,h4,h2⟩
  · rcases (show a.val.map 0 ∈ U ∪ V from by rw [hcover]; exact hstartc) with hu | hv
    · exact False.elim (hUout hu (interior_subset hstart))
    · exact False.elim (hVout hv (interior_subset hstart))
end CurveComplex.HyperellipticModel
