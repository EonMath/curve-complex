import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Topology.Homeomorph.Defs

open Set Topology

theorem actual_local_negation_quotient_literal_square_chart {E B : Type*} [TopologicalSpace E] [Nonempty E] [TopologicalSpace B]
    (V : Set ℂ) (hV : IsOpen V) (e : E ≃ₜ V) (p : E → B)
    (hp : IsOpenQuotientMap p)
    (hfiber : ∀ x y, p x = p y ↔
      (e x : ℂ) = (e y : ℂ) ∨ (e x : ℂ) = -(e y : ℂ)) :
    ∃ c : OpenPartialHomeomorph B ℂ, c.source = Set.univ ∧
      c.target = ((fun z : ℂ => z ^ 2) '' V) ∧
      (∀ x, c (p x) = (e x : ℂ) ^ 2) := by
  classical
  let W := (fun z : ℂ => z ^ 2) '' V
  have hW : IsOpen W := (Complex.isOpenQuotientMap_pow 2).isOpenMap V hV
  let k : E → W := fun x => ⟨(e x : ℂ) ^ 2, ⟨e x, (e x).property, rfl⟩⟩
  have hk : IsOpenQuotientMap k := by
    refine ⟨?_, ?_, ?_⟩
    · intro w
      obtain ⟨z, hz, heq⟩ := w.property
      refine ⟨e.symm ⟨z,hz⟩, ?_⟩
      apply Subtype.ext
      change (e (e.symm ⟨z,hz⟩) : ℂ) ^ 2 = w.val
      rw [e.apply_symm_apply]
      exact heq
    · exact (((Complex.isOpenQuotientMap_pow 2).continuous.comp
        continuous_subtype_val).comp e.continuous).subtype_mk _
    · exact (((Complex.isOpenQuotientMap_pow 2).isOpenMap.comp
        hV.isOpenEmbedding_subtypeVal.isOpenMap).comp e.isOpenMap).subtype_mk _
  have hfiber' : ∀ x y, p x = p y ↔ k x = k y := by
    intro x y
    rw [hfiber, Subtype.ext_iff]
    exact sq_eq_sq_iff_eq_or_eq_neg.symm
  let r : B → E := fun b => (hp.surjective b).choose
  have hr : ∀ b, p (r b) = b := fun b => (hp.surjective b).choose_spec
  let s : W → E := fun c => (hk.surjective c).choose
  have hs : ∀ c, k (s c) = c := fun c => (hk.surjective c).choose_spec
  let h : B → W := fun b => k (r b)
  let j : W → B := fun c => p (s c)
  have hh : ∀ x, h (p x) = k x := fun x => (hfiber' _ x).mp (hr (p x))
  have hj : ∀ x, j (k x) = p x := fun x => (hfiber' _ x).mpr (hs (k x))
  have hleft : Function.LeftInverse j h := by
    intro b
    change j (k (r b)) = b
    rw [hj, hr]
  have hright : Function.RightInverse j h := by
    intro c
    change h (p (s c)) = c
    rw [hh, hs]
  have hc : Continuous h := hp.isQuotientMap.continuous_iff.mpr (by
    convert hk.continuous using 1
    exact funext hh)
  have jc : Continuous j := hk.isQuotientMap.continuous_iff.mpr (by
    convert hp.continuous using 1
    exact funext hj)
  let e : B ≃ₜ W := {
    toFun := h
    invFun := j
    left_inv := hleft
    right_inv := hright
    continuous_toFun := hc
    continuous_invFun := jc }
  letI : Nonempty B := Nonempty.map p inferInstance
  let φ : B → ℂ := fun b => (e b : ℂ)
  have hφ : IsOpenEmbedding φ :=
    hW.isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding
  let c := hφ.toOpenPartialHomeomorph φ
  have hrange : Set.range φ = W := by
    ext z
    constructor
    · rintro ⟨b,rfl⟩
      exact (e b).property
    · intro hz
      exact ⟨e.symm ⟨z,hz⟩, congrArg Subtype.val (e.apply_symm_apply ⟨z,hz⟩)⟩
  refine ⟨c, hφ.toOpenPartialHomeomorph_source φ, ?_, ?_⟩
  · rw [hφ.toOpenPartialHomeomorph_target φ, hrange]
  · intro x
    rw [hφ.toOpenPartialHomeomorph_apply φ]
    exact congrArg Subtype.val (hh x)

