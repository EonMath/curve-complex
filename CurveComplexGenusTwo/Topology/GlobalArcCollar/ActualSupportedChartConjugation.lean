import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualAxisRectangleTransplant
import CurveComplexGenusTwo.Topology.CrosscutSupport
namespace CurveComplex
open Set Topology Schoenflies

/-- Conjugate an actually supported plane homeomorphism through a source chart,
then extend it by identity on the ambient surface. -/
theorem source_transport_supported_chart_homeomorphism
    {S : Type} [TopologicalSpace S] [T2Space S]
    (e : OpenPartialHomeomorph S Plane)
    (C O : Set Plane) (hC : IsCompact C) (hO : IsOpen O)
    (hOC : O ⊆ C) (hCt : C ⊆ e.target)
    (H : Plane ≃ₜ Plane) (hfix : ∀ z, z ∉ O → H z = z) :
    ∃ F : S ≃ₜ S,
      (∀ x, x ∉ e.source ∩ e ⁻¹' O → F x = x) ∧
      (∀ x, x ∈ e.source → e x ∈ C →
        F x ∈ e.source ∧ e (F x) = H (e x)) ∧
      (∀ x, x ∈ e.source → H (e x) = e x → F x = x) := by
  classical
  have hHC : ∀ z ∈ C, H z ∈ C := by
    intro z hz
    by_contra hn
    have hno : H z ∉ O := fun ho => hn (hOC ho)
    have he : H (H z) = H z := hfix _ hno
    have he' : H z = z := H.injective he
    exact hn (by rwa [he'])
  have hHinvfix : ∀ z, z ∉ O → H.symm z = z := by
    intro z hz
    apply H.injective
    rw [H.apply_symm_apply, hfix z hz]
  have hHinvC : ∀ z ∈ C, H.symm z ∈ C := by
    intro z hz
    by_contra hn
    have hno : H.symm z ∉ O := fun ho => hn (hOC ho)
    have he : H.symm (H.symm z) = H.symm z := hHinvfix _ hno
    have he' : H.symm z = z := H.symm.injective he
    exact hn (by rwa [he'])
  let HC : C ≃ₜ C := {
    toFun := fun z => ⟨H z,hHC z z.property⟩
    invFun := fun z => ⟨H.symm z,hHinvC z z.property⟩
    left_inv := by intro z; apply Subtype.ext; exact H.symm_apply_apply z
    right_inv := by intro z; apply Subtype.ext; exact H.apply_symm_apply z
    continuous_toFun := (H.continuous.comp continuous_subtype_val).subtype_mk _
    continuous_invFun := (H.symm.continuous.comp continuous_subtype_val).subtype_mk _
  }
  let V : Set S := e.symm '' C
  have hVc : IsCompact V := hC.image_of_continuousOn (e.symm.continuousOn.mono hCt)
  have hVs : V ⊆ e.source := by
    rintro x ⟨z,hz,rfl⟩
    exact e.map_target (hCt hz)
  have hVcoord : ∀ x ∈ V, e x ∈ C := by
    rintro x ⟨z,hz,rfl⟩
    simpa only [e.right_inv (hCt hz)] using hz
  let T : V ≃ₜ C := {
    toFun := fun x => ⟨e x,hVcoord x x.property⟩
    invFun := fun z => ⟨e.symm z,⟨z,z.property,rfl⟩⟩
    left_inv := by intro x; apply Subtype.ext; exact e.left_inv (hVs x.property)
    right_inv := by intro z; apply Subtype.ext; exact e.right_inv (hCt z.property)
    continuous_toFun :=
      (e.continuousOn.comp_continuous continuous_subtype_val
        (fun x => hVs x.property)).subtype_mk _
    continuous_invFun :=
      (e.symm.continuousOn.comp_continuous continuous_subtype_val
        (fun z => hCt z.property)).subtype_mk _
  }
  let Q : V ≃ₜ V := (T.trans HC).trans T.symm
  let W : Set S := e.source ∩ e ⁻¹' O
  have hWo : IsOpen W := e.isOpen_inter_preimage hO
  have hWV : W ⊆ V := by
    intro x hx
    refine ⟨e x,hOC hx.2,e.left_inv hx.1⟩
  have hQfix : ∀ x : V, (x : S) ∉ W → Q x = x := by
    intro x hx
    have hno : e x ∉ O := by
      intro ho
      exact hx ⟨hVs x.property,ho⟩
    apply T.injective
    simp only [Q, Homeomorph.trans_apply, T.apply_symm_apply]
    change HC (T x) = T x
    apply Subtype.ext
    exact hfix _ hno
  let F := extendClosedHomeomorph V W hVc.isClosed hWo hWV Q hQfix
  have houtside : ∀ x, x ∉ W → F x = x :=
    extendClosedHomeomorph_apply_outside V W hVc.isClosed hWo hWV Q hQfix
  have hformula : ∀ x, x ∈ V → F x = e.symm (H (e x)) := by
    intro x hx
    change (if hx : x ∈ V then (Q ⟨x,hx⟩ : S) else x) = _
    rw [dif_pos hx]
    rfl
  refine ⟨F,houtside,?_,?_⟩
  · intro x hxs hxC
    have hxV : x ∈ V := ⟨e x,hxC,e.left_inv hxs⟩
    rw [hformula x hxV]
    have hHt := hCt (hHC (e x) hxC)
    exact ⟨e.map_target hHt,e.right_inv hHt⟩
  · intro x hxs he
    by_cases hxV : x ∈ V
    · rw [hformula x hxV,he,e.left_inv hxs]
    · exact houtside x (fun hxW => hxV (hWV hxW))
end CurveComplex
#print axioms CurveComplex.source_transport_supported_chart_homeomorphism
