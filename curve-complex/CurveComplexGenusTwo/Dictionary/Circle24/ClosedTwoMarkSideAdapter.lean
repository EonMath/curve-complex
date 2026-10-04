import CurveComplexGenusTwo.Dictionary.ActualCircle24Components
open Set Topology
namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 9000000

/-- An arbitrary closed set with the prescribed circle frontier and exactly
two interior marks is the genuine two-mark Jordan closed side. Its boundary-
faithful disk chart is constructed, rather than inferred from an arbitrary
homeomorphism of a disk onto that set. -/
theorem arbitrary_two_mark_closed_side_adapter
    (M : HyperellipticModel E S) (a : Circle24 M) (D : Set S)
    (hD : IsClosed D) (hfront : frontier D=a.val.image)
    (hcount : (by classical exact (M.cover.branch.filter (· ∈ interior D)).card=2)) :
    ∃ U : Set S, ∃ d : Metric.closedBall (0:Schoenflies.Plane) 1 ≃ₜ D,
      IsOpen U ∧ IsConnected U ∧ U=interior D ∧ D=U ∪ a.val.image ∧
      (∀ z, (d z).val ∈ a.val.image ↔ ‖z.val‖=1) ∧
      (∀ z, (d z).val ∈ U ↔ ‖z.val‖<1) := by
  classical
  obtain ⟨U,V,hU,hV,hUc,hVc,hUV,hcover,dU,dV,hUb,hVb,hUi,hVi,hclU,hclV⟩ :=
    M.puncturedCircle_closedSides a.val
  have hdecomp : D=interior D ∪ a.val.image := by
    rw [← hfront]
    ext x
    simp only [frontier,hD.closure_eq,mem_sdiff,mem_union]
    exact ⟨fun hx => by by_cases hi : x ∈ interior D <;> aesop,
      fun h => h.elim (fun hi => interior_subset hi) And.left⟩
  have hid : interior D ∪ Dᶜ=a.val.imageᶜ := by
    rw [← hfront]
    ext x
    simp only [frontier,hD.closure_eq,mem_sdiff,mem_union,mem_compl_iff]
    tauto
  have hidsub : interior D ⊆ U ∪ V := by rw [hcover,← hid]; exact subset_union_left
  have hUsub : U ⊆ interior D ∪ Dᶜ := by rw [hid,← hcover]; exact subset_union_left
  have hVsub : V ⊆ interior D ∪ Dᶜ := by rw [hid,← hcover]; exact subset_union_right
  have hd : Disjoint (interior D) Dᶜ := Set.disjoint_left.mpr
    (fun _ hx hn => hn (interior_subset hx))
  have hne : (interior D).Nonempty := by
    obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0<(M.cover.branch.filter (· ∈ interior D)).card by rw [hcount]; norm_num)
    exact ⟨x,(Finset.mem_filter.mp hx).2⟩
  have hnotboth (hUI : U ⊆ interior D) (hVI : V ⊆ interior D) : False := by
    have he : M.cover.branch.filter (· ∈ interior D)=M.cover.branch := by
      apply Finset.filter_eq_self.mpr
      intro x hx
      have hnc : x ∈ a.val.imageᶜ := by
        intro hxc
        exact Set.disjoint_left.mp a.val.avoids_branch hxc hx
      have huv : x ∈ U ∪ V := hcover.symm ▸ hnc
      exact huv.elim (fun h => hUI h) (fun h => hVI h)
    have hc := hcount
    rw [he,M.cover.branch_card] at hc
    norm_num at hc
  rcases hUc.isPreconnected.subset_or_subset isOpen_interior hD.isOpen_compl hd hUsub with hUI | hUO <;>
    rcases hVc.isPreconnected.subset_or_subset isOpen_interior hD.isOpen_compl hd hVsub with hVI | hVO
  · exact False.elim (hnotboth hUI hVI)
  · have he : interior D=U := by
      apply subset_antisymm _ hUI
      intro x hx
      rcases hidsub hx with hu | hv
      · exact hu
      · exact False.elim (hVO hv (interior_subset hx))
    have heD : D=closure U := by rw [hdecomp,he,hclU]
    let d := dU.trans (Homeomorph.setCongr heD.symm)
    exact ⟨U,d,hU,hUc,he.symm,by rw [hdecomp,he],hUb,hUi⟩
  · have he : interior D=V := by
      apply subset_antisymm _ hVI
      intro x hx
      rcases hidsub hx with hu | hv
      · exact False.elim (hUO hu (interior_subset hx))
      · exact hv
    have heD : D=closure V := by rw [hdecomp,he,hclV]
    let d := dV.trans (Homeomorph.setCongr heD.symm)
    exact ⟨V,d,hV,hVc,he.symm,by rw [hdecomp,he],hVb,hVi⟩
  · obtain ⟨x,hx⟩ := hne
    rcases hidsub hx with hu | hv
    · exact False.elim (hUO hu (interior_subset hx))
    · exact False.elim (hVO hv (interior_subset hx))

end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.arbitrary_two_mark_closed_side_adapter
