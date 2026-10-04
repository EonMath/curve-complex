import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Maps.OpenQuotient

open Set Topology
universe u

theorem actual_involution_compact_hausdorff_quotient {E : Type u} [TopologicalSpace E] [T2Space E]
    [CompactSpace E] [ConnectedSpace E] (f : E ≃ₜ E)
    (hinv : Function.Involutive f) :
    ∃ (B : Type u) (t : TopologicalSpace B) (p : E → B),
      letI : TopologicalSpace B := t
      T2Space B ∧ CompactSpace B ∧ ConnectedSpace B ∧
      IsOpenQuotientMap p ∧ (∀ x y, p y = p x ↔ y = x ∨ y = f x) ∧
      (∀ x, p ⁻¹' {p x} = {x, f x}) := by
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
    hq.surjective.connectedSpace hq.continuous, hq, hp, ?_⟩
  intro x
  ext y
  exact hp x y
