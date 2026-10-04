import CurveComplexGenusTwo.Topology.ActualMain14Dictionary.Providers.Main14ActualPairedStrictBigon
import CurveComplexGenusTwo.Dictionary.CoverClassification.CoverReductions

namespace CurveComplex.BranchedDoubleCover
open Set Topology
set_option maxHeartbeats 4000000

/-- Descend an actual deck-commuting isotopy through the original branched
projection. Joint continuity is obtained from the actual quotient projection,
not assumed downstairs. -/
theorem actual_deck_equivariant_isotopy_descends
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [CompactSpace E] [CompactSpace S] [T2Space S]
    (q : BranchedDoubleCover E S) (K : AmbientIsotopy E)
    (heq : ∀ t x, K.map (t,q.deck x) = q.deck (K.map (t,x)))
    (hfix : ∀ t x, q.projection x ∈ q.branch → K.map (t,x) = x) :
    ∃ L : AmbientIsotopy S,
      (∀ t x, L.map (t,q.projection x) = q.projection (K.map (t,x))) ∧
      (∀ t b, b ∈ q.branch → L.map (t,b) = b) := by
  classical
  let lift : S → E := fun y => Classical.choose (q.projection_surjective y)
  have hlift (y : S) : q.projection (lift y) = y := Classical.choose_spec (q.projection_surjective y)
  let f : Interval × S → S := fun p => q.projection (K.map (p.1,lift p.2))
  have hf (t : Interval) (x : E) : f (t,q.projection x) = q.projection (K.map (t,x)) := by
    have hp : q.projection x = q.projection (lift (q.projection x)) := (hlift _).symm
    rcases (q.fiber_pair _ _).mp hp with hh | hh
    · simp only [f,hh]
    · simp only [f,hh,heq,q.projection_deck]
  have hfcont : Continuous f := q.projection_isQuotientMap.continuous_lift_prod_right (by
    have h := q.projection_continuous.comp K.map.continuous
    exact h.congr (fun p => (hf p.1 p.2).symm))
  have hbij (t : Interval) : Function.Bijective (fun y => f (t,y)) := by
    obtain ⟨e,he⟩ := K.homeomorphism_at t
    constructor
    · intro y z hyz
      have hp : q.projection (K.map (t,lift y)) = q.projection (K.map (t,lift z)) := hyz
      rcases (q.fiber_pair _ _).mp hp with hh | hh
      · have hz : lift z = lift y := e.injective (by simpa only [he] using hh)
        exact (hlift y).symm.trans ((congrArg q.projection hz).symm.trans (hlift z))
      · have hz : lift z = q.deck (lift y) := e.injective (by simpa only [he,heq] using hh)
        calc
          y = q.projection (lift y) := (hlift y).symm
          _ = q.projection (q.deck (lift y)) := (q.projection_deck _).symm
          _ = q.projection (lift z) := congrArg q.projection hz.symm
          _ = z := hlift z
    · intro y
      obtain ⟨x,hx⟩ := q.projection_surjective y
      refine ⟨q.projection (e.symm x),?_⟩
      change f (t,q.projection (e.symm x)) = y
      rw [hf,← he,e.apply_symm_apply,hx]
  let L : AmbientIsotopy S := {
    map := ⟨f,hfcont⟩
    homeomorphism_at := by
      intro t
      have hc : Continuous (fun y => f (t,y)) := hfcont.comp (continuous_const.prodMk continuous_id)
      let e := (isHomeomorph_iff_continuous_bijective.mpr ⟨hc,hbij t⟩).homeomorph (fun y => f (t,y))
      exact ⟨e,fun x => rfl⟩
    at_zero := by
      intro y
      change q.projection (K.map (⟨0,by norm_num⟩,lift y)) = y
      rw [K.at_zero,hlift] }
  refine ⟨L,hf,?_⟩
  intro t b hb
  change q.projection (K.map (t,lift b)) = b
  rw [hfix t _ (by rw [hlift]; exact hb),hlift]
end CurveComplex.BranchedDoubleCover
