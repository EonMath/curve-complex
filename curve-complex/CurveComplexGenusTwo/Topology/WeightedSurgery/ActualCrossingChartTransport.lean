import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualMarkedCrossingTransport

namespace CurveComplex.HyperellipticModel.ArcSurgery
open Set
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section

theorem actual_crossesInDisk_transport_preserving_anchor_image
    (M : HyperellipticModel E S) (anchor b : EssentialMarkedArc M)
    (h : S ≃ₜ S) (hm : ∀ z, z ∈ M.cover.branch → h z = z)
    (ha : h '' anchor.val.image = anchor.val.image)
    (p : S) (hc : CrossesInDisk M anchor b p) :
    CrossesInDisk M anchor (b.transport h hm) (h p) := by
  obtain ⟨U,hU,hp,hmark,e,he0,hanchor,hb⟩ := hc
  let eU : U ≃ₜ (h '' U) := h.image U
  have hp' : h p ∈ h '' U := mem_image_of_mem h hp
  let f := eU.symm.trans e
  have hmark' : Disjoint (h '' U) (M.cover.branch : Set S) := by
    apply Set.disjoint_left.mpr
    rintro q ⟨z,hz,rfl⟩ hq
    have heq : h z = z := h.injective (hm (h z) hq)
    exact Set.disjoint_left.mp hmark hz (heq ▸ hq)
  refine ⟨h '' U,h.isOpenMap U hU,hp',hmark',f,?_,?_,?_⟩
  · have he : eU.symm ⟨h p,hp'⟩ = ⟨p,hp⟩ := by
      apply Subtype.ext
      exact h.symm_apply_apply p
    simpa only [f,Homeomorph.trans_apply,he] using he0
  · intro q
    let y := eU.symm q
    have hy : y.val = h.symm q.val := rfl
    have hmem : q.val ∈ h '' anchor.val.image ↔ y.val ∈ anchor.val.image := by
      rw [hy]
      exact Set.mem_image_iff_of_inverse h.symm_apply_apply h.apply_symm_apply
    rw [ha] at hmem
    exact hmem.trans (hanchor y)
  · intro q
    let y := eU.symm q
    have hy : y.val = h.symm q.val := rfl
    change q.val ∈ (b.val.transport h hm).image ↔ _
    rw [MarkedArc.transport_image]
    have hmem : q.val ∈ h '' b.val.image ↔ y.val ∈ b.val.image := by
      rw [hy]
      exact Set.mem_image_iff_of_inverse h.symm_apply_apply h.apply_symm_apply
    exact hmem.trans (hb y)

end
end CurveComplex.HyperellipticModel.ArcSurgery
