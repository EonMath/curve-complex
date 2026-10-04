/-
The gluing construction here uses Schoenflies.MatchedArc.lean and its
ArcHomeo API. Copyright (c) 2026 Álvaro Begué. Released under Apache 2.0.
-/
import Schoenflies.MatchedArc
import Schoenflies.Topology

open Set

namespace Schoenflies

/-- Glue two endpoint-matched arc homeomorphisms along their common endpoints.
The resulting boundary homeomorphism carries the second source arc onto the
second target arc. -/
theorem exists_homeomorph_union_arcs_preserving_second
    {A P B Q : Set Plane} {a b c d : Plane}
    (hA : IsArcBetween A a b) (hP : IsArcBetween P a b)
    (hB : IsArcBetween B c d) (hQ : IsArcBetween Q c d)
    (hsrc : A ∩ P = {a, b}) (htgt : B ∩ Q = {c, d}) :
    ∃ e : ↥(A ∪ P) ≃ₜ ↥(B ∪ Q),
      Subtype.val '' (e '' {x : ↥(A ∪ P) | (x : Plane) ∈ P}) = Q ∧
      e ⟨a, Or.inl hA.left_mem⟩ = ⟨c, Or.inl hB.left_mem⟩ ∧
      e ⟨b, Or.inl hA.right_mem⟩ = ⟨d, Or.inl hB.right_mem⟩ := by
  classical
  obtain ⟨eA⟩ := exists_arcHomeo hA hB
  obtain ⟨eP⟩ := exists_arcHomeo hP hQ
  let f : Plane → Plane := fun x => if x ∈ A then eA.toFun x else eP.toFun x
  have hagree : ∀ x, x ∈ A ∩ P → eA.toFun x = eP.toFun x := by
    intro x hx
    have hx' : x = a ∨ x = b := by
      have : x ∈ ({a, b} : Set Plane) := hsrc ▸ hx
      simpa using this
    rcases hx' with rfl | rfl
    · rw [eA.map_left, eP.map_left]
    · rw [eA.map_right, eP.map_right]
  have hf_onA : ∀ x ∈ A, f x = eA.toFun x := by
    intro x hx
    simp [f, hx]
  have hf_onP : ∀ x ∈ P, f x = eP.toFun x := by
    intro x hx
    by_cases hxA : x ∈ A
    · simp [f, hxA, hagree x ⟨hxA, hx⟩]
    · simp [f, hxA]
  have hfA : ContinuousOn f A := by
    apply eA.continuousOn_toFun.congr
    intro x hx
    exact hf_onA x hx
  have hfP : ContinuousOn f P := by
    apply eP.continuousOn_toFun.congr
    intro x hx
    exact hf_onP x hx
  have hf : ContinuousOn f (A ∪ P) :=
    Plane.continuousOn_union_of_isClosed hA.isArc.isCompact.isClosed
      hP.isArc.isCompact.isClosed hfA hfP
  have hf_maps : MapsTo f (A ∪ P) (B ∪ Q) := by
    intro x hx
    rcases hx with hxA | hxP
    · rw [hf_onA x hxA]
      exact Or.inl (eA.mapsTo hxA)
    · rw [hf_onP x hxP]
      exact Or.inr (eP.mapsTo hxP)
  have hfP_image : f '' P = Q := by
    apply Subset.antisymm
    · rintro y ⟨x, hxP, rfl⟩
      rw [hf_onP x hxP]
      exact eP.mapsTo hxP
    · intro y hy
      rw [← eP.image_eq] at hy
      obtain ⟨x, hxP, hxy⟩ := hy
      refine ⟨x, hxP, ?_⟩
      exact (hf_onP x hxP).trans hxy
  have hinj : InjOn f (A ∪ P) := by
    intro x hx y hy hxy
    rcases hx with hxA | hxP
    · rcases hy with hyA | hyP
      · exact eA.injOn hxA hyA ((hf_onA x hxA).symm.trans (hxy.trans (hf_onA y hyA)))
      · have hcross : eA.toFun x = eP.toFun y :=
          (hf_onA x hxA).symm.trans (hxy.trans (hf_onP y hyP))
        have hxy' : eA.toFun x ∈ B ∩ Q :=
          ⟨eA.mapsTo hxA, hcross ▸ eP.mapsTo hyP⟩
        have hend : eA.toFun x = c ∨ eA.toFun x = d := by
          have : eA.toFun x ∈ ({c, d} : Set Plane) := htgt ▸ hxy'
          simpa using this
        rcases hend with hc | hd
        · have hxEq : eA.toFun x = eA.toFun a := by rw [hc, eA.map_left]
          have hyEq : eP.toFun y = eP.toFun a := by
            calc
              eP.toFun y = eA.toFun x := hcross.symm
              _ = c := hc
              _ = eP.toFun a := eP.map_left.symm
          have hxa : x = a := eA.injOn hxA hA.left_mem hxEq
          have hya : y = a := eP.injOn hyP hP.left_mem hyEq
          exact hxa.trans hya.symm
        · have hxEq : eA.toFun x = eA.toFun b := by rw [hd, eA.map_right]
          have hyEq : eP.toFun y = eP.toFun b := by
            calc
              eP.toFun y = eA.toFun x := hcross.symm
              _ = d := hd
              _ = eP.toFun b := eP.map_right.symm
          have hxb : x = b := eA.injOn hxA hA.right_mem hxEq
          have hyb : y = b := eP.injOn hyP hP.right_mem hyEq
          exact hxb.trans hyb.symm
    · rcases hy with hyA | hyP
      · have hcross : eP.toFun x = eA.toFun y :=
          (hf_onP x hxP).symm.trans (hxy.trans (hf_onA y hyA))
        have hxy' : eA.toFun y ∈ B ∩ Q :=
          ⟨eA.mapsTo hyA, hcross.symm ▸ eP.mapsTo hxP⟩
        have hend : eA.toFun y = c ∨ eA.toFun y = d := by
          have : eA.toFun y ∈ ({c, d} : Set Plane) := htgt ▸ hxy'
          simpa using this
        rcases hend with hc | hd
        · have hyEq : eA.toFun y = eA.toFun a := by rw [hc, eA.map_left]
          have hxEq : eP.toFun x = eP.toFun a := by
            calc
              eP.toFun x = eA.toFun y := hcross
              _ = c := hc
              _ = eP.toFun a := eP.map_left.symm
          have hya : y = a := eA.injOn hyA hA.left_mem hyEq
          have hxa : x = a := eP.injOn hxP hP.left_mem hxEq
          exact hxa.trans hya.symm
        · have hyEq : eA.toFun y = eA.toFun b := by rw [hd, eA.map_right]
          have hxEq : eP.toFun x = eP.toFun b := by
            calc
              eP.toFun x = eA.toFun y := hcross
              _ = d := hd
              _ = eP.toFun b := eP.map_right.symm
          have hyb : y = b := eA.injOn hyA hA.right_mem hyEq
          have hxb : x = b := eP.injOn hxP hP.right_mem hxEq
          exact hxb.trans hyb.symm
      · exact eP.injOn hxP hyP ((hf_onP x hxP).symm.trans (hxy.trans (hf_onP y hyP)))
  have hsurj : Function.Surjective (fun x : ↥(A ∪ P) => (⟨f x, hf_maps x.2⟩ : ↥(B ∪ Q))) := by
    intro y
    rcases y.2 with hyB | hyQ
    · have hyB' : y.1 ∈ B := hyB
      have hyBimage : y.1 ∈ eA.toFun '' A := by rw [eA.image_eq]; exact hyB'
      clear hyB'
      obtain ⟨x, hxA, hxy⟩ := hyBimage
      refine ⟨⟨x, Or.inl hxA⟩, ?_⟩
      apply Subtype.ext
      exact (hf_onA x hxA).trans hxy
    · have hyQ' : y.1 ∈ Q := hyQ
      have hyQimage : y.1 ∈ eP.toFun '' P := by rw [eP.image_eq]; exact hyQ'
      clear hyQ'
      obtain ⟨x, hxP, hxy⟩ := hyQimage
      refine ⟨⟨x, Or.inr hxP⟩, ?_⟩
      apply Subtype.ext
      exact (hf_onP x hxP).trans hxy
  let E : ↥(A ∪ P) → ↥(B ∪ Q) := fun x => ⟨f x, hf_maps x.2⟩
  have hEcont : Continuous E := hf.domRestrict.subtype_mk _
  have hEinj : Function.Injective E := by
    intro x y hxy
    apply Subtype.ext
    exact hinj x.property y.property (congrArg Subtype.val hxy)
  have : CompactSpace ↥(A ∪ P) :=
    isCompact_iff_compactSpace.mp (hA.isArc.isCompact.union hP.isArc.isCompact)
  let e : ↥(A ∪ P) ≃ₜ ↥(B ∪ Q) :=
    hEcont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective E ⟨hEinj, hsurj⟩)
  have hArcImage :
      Subtype.val '' (e '' {x : ↥(A ∪ P) | (x : Plane) ∈ P}) = Q := by
    rw [Set.image_image]
    ext y
    constructor
    · rintro ⟨x, hxP, rfl⟩
      change f (x : Plane) ∈ Q
      rw [hf_onP x hxP]
      exact eP.mapsTo hxP
    · intro hyQ
      have hyImage : y ∈ f '' P := by rw [hfP_image]; exact hyQ
      obtain ⟨x, hxP, hxy⟩ := hyImage
      exact ⟨⟨x, Or.inr hxP⟩, hxP, hxy⟩
  have hleft : e ⟨a, Or.inl hA.left_mem⟩ = ⟨c, Or.inl hB.left_mem⟩ := by
    apply Subtype.ext
    change f a = c
    simp [f, hA.left_mem, eA.map_left]
  have hright : e ⟨b, Or.inl hA.right_mem⟩ = ⟨d, Or.inl hB.right_mem⟩ := by
    apply Subtype.ext
    change f b = d
    simp [f, hA.right_mem, eA.map_right]
  exact ⟨e, hArcImage, hleft, hright⟩

end Schoenflies

#print axioms Schoenflies.exists_homeomorph_union_arcs_preserving_second
