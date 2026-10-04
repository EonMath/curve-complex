import CurveComplexGenusTwo.Dictionary.BranchedCover
import CurveComplexGenusTwo.Foundations.Definitions

namespace CurveComplex.BranchedDoubleCover
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]

/-- A supported actual operation and its disjoint deck-conjugate produce an
actual deck-commuting ambient isotopy. This is a construction, not an assumed
equivariant representative or an equivariance certificate. -/
theorem supported_paired_deck_operation
    (q : BranchedDoubleCover E S) (H : AmbientIsotopy E)
    (V : Set E) (hsep : Disjoint V (q.deck '' V))
    (hfix : ∀ t x, x ∉ V → H.map (t,x) = x) :
    ∃ K : AmbientIsotopy E,
      (∀ t x, K.map (t,x) = q.deck (H.map (t,q.deck (H.map (t,x))))) ∧
      (∀ t x, K.map (t,q.deck x) = q.deck (K.map (t,x))) ∧
      (∀ t x, x ∈ V → K.map (t,x) = H.map (t,x)) ∧
      (∀ t x, x ∈ q.deck '' V → K.map (t,x) = q.deck (H.map (t,q.deck x))) ∧
      (∀ t x, x ∉ V ∪ q.deck '' V → K.map (t,x) = x) ∧
      (∀ t x, q.projection x ∈ q.branch → K.map (t,x) = x) := by
  classical
  have hHV (t : Interval) (x : E) (hx : x ∈ V) : H.map (t,x) ∈ V := by
    by_contra hn
    obtain ⟨e,he⟩ := H.homeomorphism_at t
    have hsame : H.map (t,H.map (t,x)) = H.map (t,x) := hfix t _ hn
    have hi : H.map (t,x) = x := e.injective (by simpa only [← he] using hsame)
    exact hn (hi.symm ▸ hx)
  have hJV (t : Interval) (x : E) (hx : x ∈ q.deck '' V) :
      q.deck (H.map (t,q.deck x)) ∈ q.deck '' V := by
    obtain ⟨y,hy,rfl⟩ := hx
    rw [q.deck_involution]
    exact Set.mem_image_of_mem q.deck (hHV t y hy)
  have hJfix (t : Interval) (x : E) (hx : x ∉ q.deck '' V) :
      q.deck (H.map (t,q.deck x)) = x := by
    have hτx : q.deck x ∉ V := by
      intro hh
      exact hx ⟨q.deck x,hh,q.deck_involution x⟩
    rw [hfix t _ hτx,q.deck_involution]
  have hCommute (t : Interval) (x : E) :
      H.map (t,q.deck (H.map (t,q.deck x))) =
        q.deck (H.map (t,q.deck (H.map (t,x)))) := by
    by_cases hx : x ∈ V
    · have hxW : x ∉ q.deck '' V := fun hh => Set.disjoint_left.mp hsep hx hh
      have hHxW : H.map (t,x) ∉ q.deck '' V :=
        fun hh => Set.disjoint_left.mp hsep (hHV t x hx) hh
      rw [hJfix t x hxW,hJfix t _ hHxW]
    by_cases hxW : x ∈ q.deck '' V
    · have hJxV : q.deck (H.map (t,q.deck x)) ∉ V :=
        fun hh => Set.disjoint_left.mp hsep hh (hJV t x hxW)
      rw [hfix t x hx,hfix t _ hJxV]
    · rw [hfix t x hx,hJfix t x hxW,hfix t x hx]
  let K : AmbientIsotopy E := {
    map := ⟨fun z => q.deck (H.map (z.1,q.deck (H.map z))),by fun_prop⟩
    homeomorphism_at := by
      intro t
      obtain ⟨e,he⟩ := H.homeomorphism_at t
      refine ⟨((e.trans q.deck).trans e).trans q.deck,?_⟩
      intro x
      change q.deck (e (q.deck (e x))) = q.deck (H.map (t,q.deck (H.map (t,x))))
      rw [he,he]
    at_zero := by
      intro x
      change q.deck (H.map (⟨0,by norm_num⟩,q.deck (H.map (⟨0,by norm_num⟩,x)))) = x
      rw [H.at_zero,H.at_zero,q.deck_involution] }
  have hK (t : Interval) (x : E) : K.map (t,x) = q.deck (H.map (t,q.deck (H.map (t,x)))) := rfl
  refine ⟨K,hK,?_,?_,?_,?_,?_⟩
  · intro t x
    rw [hK,hK,q.deck_involution]
    have hh := hCommute t (q.deck x)
    rw [q.deck_involution] at hh
    exact hh.symm
  · intro t x hx
    rw [hK]
    have hτHx : q.deck (H.map (t,x)) ∉ V := by
      intro hh
      exact Set.disjoint_left.mp hsep hh (Set.mem_image_of_mem q.deck (hHV t x hx))
    rw [hfix t _ hτHx,q.deck_involution]
  · intro t x hx
    rw [hK,hfix t x (fun hh => Set.disjoint_left.mp hsep hh hx)]
  · intro t x hx
    rw [hK,hfix t x (fun hh => hx (Or.inl hh)),hJfix t x (fun hh => hx (Or.inr hh))]
  · intro t x hxR
    have hfixed : q.deck x = x := (q.fixed_iff_branch x).mpr hxR
    have hxV : x ∉ V := by
      intro hx
      exact Set.disjoint_left.mp hsep hx ⟨x,hx,hfixed⟩
    have hxτV : q.deck x ∉ V := by simpa [hfixed] using hxV
    rw [hK,hfix t x hxV,hfix t _ hxτV,q.deck_involution]
end CurveComplex.BranchedDoubleCover
