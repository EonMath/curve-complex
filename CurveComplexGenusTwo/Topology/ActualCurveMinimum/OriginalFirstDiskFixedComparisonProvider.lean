import CurveComplexGenusTwo.Foundations.ActualIntersectionBridge
import Mathlib

namespace CurveComplex.LocalSurgery

/- Source reduction before the bigon criterion: the comparison curve can be
   kept literally fixed while the other representative realizes the true minimum.
   This does not claim that an arbitrary such replacement respects other curves. -/
theorem audited_fixed_comparison_minimum {S : Type} [TopologicalSpace S]
    (a b : EssentialCurve S) (ht : Transverse a.val b.val) :
    ∃ a' : EssentialCurve S,
      AmbientIsotopy.Rel a.val.image a'.val.image ∧
      ∃ ht' : Transverse a'.val b.val,
        ht'.1.toFinset.card = geometricIntersection
          (Quotient.mk (essentialCurveSetoid S) a)
          (Quotient.mk (essentialCurveSetoid S) b) := by
  have transfer (c d c₁ d₁ : Curve S) (e : S ≃ₜ S)
      (hc : ∀ x, x ∈ c.image ↔ e x ∈ c₁.image)
      (hd : ∀ x, x ∈ d.image ↔ e x ∈ d₁.image)
      (ht₁ : Transverse c₁ d₁) :
      ∃ h : Transverse c d, h.1.toFinset.card = ht₁.1.toFinset.card := by
    have hset : c.image ∩ d.image = e ⁻¹' (c₁.image ∩ d₁.image) := by
      ext x
      exact and_congr (hc x) (hd x)
    have hf : (c.image ∩ d.image).Finite := by
      rw [hset]
      exact ht₁.1.preimage e.injective.injOn
    have hcross : ∀ p ∈ c.image ∩ d.image, CrossesAt c d p := by
      intro p hp
      have hep : e p ∈ c₁.image ∩ d₁.image := ⟨(hc p).mp hp.1,(hd p).mp hp.2⟩
      obtain ⟨U,V,hpU,h,hU,hV,hzero,haxes⟩ := ht₁.2 (e p) hep
      let U' : Set S := e ⁻¹' U
      let φ : U' ≃ₜ U := {
        toFun := fun x => ⟨e x,x.property⟩
        invFun := fun x => ⟨e.symm x,by change e (e.symm x) ∈ U; simpa using x.property⟩
        left_inv := by intro x; apply Subtype.ext; exact e.symm_apply_apply x
        right_inv := by intro x; apply Subtype.ext; exact e.apply_symm_apply x
        continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk (fun x => x.property)
        continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk (fun x => by
          change e (e.symm x) ∈ U
          simpa using x.property) }
      refine ⟨U',V,hpU,φ.trans h,hU.preimage e.continuous,hV,hzero,?_⟩
      intro x hx
      exact ⟨(hc x).trans (haxes (e x) hx).1,(hd x).trans (haxes (e x) hx).2⟩
    let h : Transverse c d := ⟨hf,hcross⟩
    refine ⟨h,?_⟩
    rw [← Set.ncard_eq_toFinset_card _ h.1,← Set.ncard_eq_toFinset_card _ ht₁.1,hset]
    exact Set.ncard_preimage_of_injective_subset_range e.injective (by
      rw [e.surjective.range_eq]; exact Set.subset_univ _)
  let counts := intersectionCounts (Quotient.mk (essentialCurveSetoid S) a)
    (Quotient.mk (essentialCurveSetoid S) b)
  have hne : counts.Nonempty := ⟨ht.1.toFinset.card,a,b,rfl,rfl,ht,rfl⟩
  obtain ⟨a₁,b₁,ha₁,hb₁,ht₁,hn⟩ := Nat.sInf_mem hne
  have haRel : AmbientIsotopy.Rel a.val.image a₁.val.image := Quotient.exact ha₁.symm
  have hbRel : AmbientIsotopy.Rel b.val.image b₁.val.image := Quotient.exact hb₁.symm
  obtain ⟨H,hH⟩ := hbRel
  let one : Interval := ⟨1,by norm_num⟩
  obtain ⟨e,he⟩ := H.homeomorphism_at one
  have heH : (e : S → S) = H.finalMap := funext he
  have heb : e '' b.val.image = b₁.val.image := heH ▸ hH
  let c : Curve S := ⟨e.symm ∘ a₁.val.map,e.symm.isEmbedding.comp a₁.val.embedded⟩
  have hcimage : c.image = e.symm '' a₁.val.image := Set.range_comp e.symm a₁.val.map
  have hec : e '' c.image = a₁.val.image := by
    rw [hcimage,Set.image_image]
    simp
  have hcRel : AmbientIsotopy.Rel c.image a₁.val.image := ⟨H,heH ▸ hec⟩
  have hac : AmbientIsotopy.Rel a.val.image c.image :=
    ambientIsotopy_equivalence.trans haRel (ambientIsotopy_equivalence.symm hcRel)
  let a' : EssentialCurve S := ⟨c,(essential_isotopy_invariant hac).mp a.property⟩
  have hcmem (x : S) : x ∈ c.image ↔ e x ∈ a₁.val.image := by
    rw [← hec]
    simp only [Set.mem_image, e.injective.eq_iff, exists_eq_right]
  have hbmem (x : S) : x ∈ b.val.image ↔ e x ∈ b₁.val.image := by
    rw [← heb]
    simp only [Set.mem_image, e.injective.eq_iff, exists_eq_right]
  obtain ⟨ht',hcard⟩ := transfer c b.val a₁.val b₁.val e hcmem hbmem ht₁
  exact ⟨a',hac,ht',hcard.trans hn.symm⟩

end CurveComplex.LocalSurgery
