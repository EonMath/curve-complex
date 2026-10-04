import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Maps.OpenQuotient

open Set Topology
universe u

theorem actual_involution_global_six_branch_quotient_assembly {E : Type u} [TopologicalSpace E] [T2Space E]
    [CompactSpace E] [ConnectedSpace E] (f : E ≃ₜ E)
    (hinv : Function.Involutive f) (F : Finset E)
    (hfix : (F : Set E) = {x | f x = x}) (hcard : F.card = 6) :
    ∃ (B : Type u) (t : TopologicalSpace B) (p : E → B),
      letI : TopologicalSpace B := t
      T2Space B ∧ CompactSpace B ∧ ConnectedSpace B ∧
      IsOpenQuotientMap p ∧ (∀ x y, p y = p x ↔ y = x ∨ y = f x) ∧
      IsLocalHomeomorphOn p {x | f x ≠ x} ∧
      ∃ D : Finset B, D.card = 6 ∧ (D : Set B) = p '' {x | f x = x} ∧
      (∀ x, p x ∈ D ↔ f x = x) ∧
      (∀ x, f x = x → p ⁻¹' {p x} = {x}) ∧
      (∀ x, f x ≠ x → (p ⁻¹' {p x}).Finite ∧ (p ⁻¹' {p x}).ncard = 2) := by
  have hglobal :
    ∃ (B : Type u) (t : TopologicalSpace B) (p : E → B),
      letI : TopologicalSpace B := t
      T2Space B ∧ CompactSpace B ∧ ConnectedSpace B ∧
      IsOpenQuotientMap p ∧ (∀ x y, p y = p x ↔ y = x ∨ y = f x) ∧
      (∀ x, p ⁻¹' {p x} = {x, f x}) ∧
      IsLocalHomeomorphOn p {x | f x ≠ x} := by
    let r : Setoid E := {
      r := fun x y => x = y ∨ x = f y
      iseqv := {
        refl := fun x => Or.inl rfl
        symm := by
          intro x y h
          rcases h with h | h
          · exact Or.inl h.symm
          · exact Or.inr (by rw [h, hinv y])
        trans := by
          intro x y z hxy hyz
          rcases hxy with hxy | hxy <;> rcases hyz with hyz | hyz
          · exact Or.inl (hxy.trans hyz)
          · exact Or.inr (hxy.trans hyz)
          · exact Or.inr (by rw [hxy, hyz])
          · exact Or.inl (by rw [hxy, hyz, hinv z]) } }
    let B := Quotient r
    let p : E → B := Quotient.mk r
    have hp : ∀ x y, p y = p x ↔ y = x ∨ y = f x := by
      intro x y
      exact Quotient.eq
    have hopen : IsOpenMap p := by
      intro U hU
      rw [← isQuotientMap_quotient_mk'.isOpen_preimage]
      have he : p ⁻¹' (p '' U) = U ∪ f ⁻¹' U := by
        ext x
        constructor
        · rintro ⟨y, hy, h⟩
          rcases (hp x y).mp h with h | h
          · exact Or.inl (h ▸ hy)
          · exact Or.inr (show f x ∈ U from h ▸ hy)
        · rintro (h | h)
          · exact ⟨x, h, rfl⟩
          · exact ⟨f x, h, (hp x (f x)).mpr (Or.inr rfl)⟩
      change IsOpen (p ⁻¹' (p '' U))
      rw [he]
      exact hU.union (hU.preimage f.continuous)
    have hq : IsOpenQuotientMap p :=
      ⟨Quotient.mk_surjective, continuous_quotient_mk', hopen⟩
    have hclosed : IsClosed {q : E × E | p q.1 = p q.2} := by
      have he : {q : E × E | p q.1 = p q.2} =
          {q : E × E | q.1 = q.2} ∪ {q : E × E | q.1 = f q.2} := by
        ext q
        exact hp q.2 q.1
      rw [he]
      exact (isClosed_eq continuous_fst continuous_snd).union
        (isClosed_eq continuous_fst (f.continuous.comp continuous_snd))
    letI : T2Space B := (t2Space_iff_of_isOpenQuotientMap hq).mpr hclosed
    refine ⟨B, inferInstance, p, inferInstance, inferInstance,
      hq.surjective.connectedSpace hq.continuous, hq, hp, ?_, ?_⟩
    · intro x
      ext y
      exact hp x y
    · intro x hx
      obtain ⟨V, W, hV, hW, hxV, hfxW, hVW⟩ := t2_separation hx.symm
      let U := V ∩ f ⁻¹' W
      have hU : IsOpen U := hV.inter (hW.preimage f.continuous)
      have hxU : x ∈ U := ⟨hxV, hfxW⟩
      have hinj : Set.InjOn p U := by
        intro y hy z hz hyz
        rcases (hp z y).mp hyz with heq | heq
        · exact heq
        · exfalso
          have hyW : y ∈ W := heq ▸ hz.2
          exact Set.disjoint_left.mp hVW hy.1 hyW
      letI : Nonempty E := ⟨x⟩
      exact ⟨OpenPartialHomeomorph.ofContinuousOpenRestrict hinj.toPartialEquiv
        hq.continuous.continuousOn
        (hq.isOpenMap.comp hU.isOpenEmbedding_subtypeVal.isOpenMap) hU, hxU, rfl⟩
  obtain ⟨B, t, p, hT, hC, hConn, hp, hfiber, hpair, hreg⟩ := hglobal
  letI : TopologicalSpace B := t
  refine ⟨B, t, p, hT, hC, hConn, hp, hfiber, hreg, ?_⟩
  have hsix :
    ∃ D : Finset B, D.card = 6 ∧ (D : Set B) = p '' {x | f x = x} ∧
      (∀ x, p x ∈ D ↔ f x = x) ∧
      (∀ x, f x = x → p ⁻¹' {p x} = {x}) ∧
      (∀ x, f x ≠ x → (p ⁻¹' {p x}).Finite ∧ (p ⁻¹' {p x}).ncard = 2) := by
    classical
    have hinj : Set.InjOn p (F : Set E) := by
      intro x hx y hy hxy
      have hyfix : f y = y := by rw [hfix] at hy; exact hy
      rcases (hfiber y x).mp hxy with h | h
      · exact h
      · exact h.trans hyfix
    refine ⟨F.image p, (Finset.card_image_of_injOn hinj).trans hcard, ?_, ?_, ?_, ?_⟩
    · rw [Finset.coe_image, hfix]
    · intro x
      constructor
      · intro hx
        obtain ⟨y, hy, hpx⟩ := Finset.mem_image.mp hx
        have hyfix : f y = y := by have hh : y ∈ (F : Set E) := hy; rw [hfix] at hh; exact hh
        have hxy : x = y := by
          rcases (hfiber y x).mp hpx.symm with h | h
          · exact h
          · exact h.trans hyfix
        simpa [hxy] using hyfix
      · intro hx
        have hh : x ∈ (F : Set E) := by
          rw [hfix]
          exact hx
        exact Finset.mem_image.mpr ⟨x, hh, rfl⟩
    · intro x hx
      ext y
      simp only [mem_preimage, mem_singleton_iff, hfiber x y, hx, or_self]
    · intro x hx
      have he : p ⁻¹' {p x} = {x, f x} := by ext y; exact hfiber x y
      rw [he]
      exact ⟨Set.toFinite _, Set.ncard_pair hx.symm⟩
  exact hsix
