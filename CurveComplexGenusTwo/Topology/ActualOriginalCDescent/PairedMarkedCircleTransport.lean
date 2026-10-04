import CurveComplexGenusTwo.Dictionary.CoverClassification.CoverReductions
import CurveComplexGenusTwo.Topology.ActualMain14CNext.Providers.Main14ActualMarkedCircleTransport

namespace CurveComplex.BranchedDoubleCover
open Set Topology

theorem paired_deck_equivariant_isotopy_descends
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [CompactSpace E] [CompactSpace S] [T2Space S]
    (q : BranchedDoubleCover E S) (K : AmbientIsotopy E)
    (heq : ∀ t x, K.map (t, q.deck x) = q.deck (K.map (t, x)))
    (hfix : ∀ t x, q.projection x ∈ q.branch → K.map (t, x) = x) :
    ∃ L : AmbientIsotopy S,
      (∀ t x, L.map (t, q.projection x) = q.projection (K.map (t, x))) ∧
      (∀ t b, b ∈ q.branch → L.map (t, b) = b) := by
  classical
  let lift : S → E := fun y => Classical.choose (q.projection_surjective y)
  have hlift (y : S) : q.projection (lift y) = y :=
    Classical.choose_spec (q.projection_surjective y)
  let f : Interval × S → S :=
    fun p => q.projection (K.map (p.1, lift p.2))
  have hf (t : Interval) (x : E) :
      f (t, q.projection x) = q.projection (K.map (t, x)) := by
    have hp : q.projection x = q.projection (lift (q.projection x)) :=
      (hlift _).symm
    rcases (q.fiber_pair _ _).mp hp with hh | hh
    · simp only [f, hh]
    · simp only [f, hh, heq, q.projection_deck]
  have hfcont : Continuous f :=
    q.projection_isQuotientMap.continuous_lift_prod_right (by
      have h := q.projection_continuous.comp K.map.continuous
      exact h.congr (fun p => (hf p.1 p.2).symm))
  have hbij (t : Interval) : Function.Bijective (fun y => f (t, y)) := by
    obtain ⟨e, he⟩ := K.homeomorphism_at t
    constructor
    · intro y z hyz
      have hp : q.projection (K.map (t, lift y)) =
          q.projection (K.map (t, lift z)) := hyz
      rcases (q.fiber_pair _ _).mp hp with hh | hh
      · have hz : lift z = lift y := e.injective (by simpa only [he] using hh)
        exact (hlift y).symm.trans
          ((congrArg q.projection hz).symm.trans (hlift z))
      · have hz : lift z = q.deck (lift y) :=
          e.injective (by simpa only [he, heq] using hh)
        calc
          y = q.projection (lift y) := (hlift y).symm
          _ = q.projection (q.deck (lift y)) :=
            (q.projection_deck _).symm
          _ = q.projection (lift z) := congrArg q.projection hz.symm
          _ = z := hlift z
    · intro y
      obtain ⟨x, hx⟩ := q.projection_surjective y
      refine ⟨q.projection (e.symm x), ?_⟩
      change f (t, q.projection (e.symm x)) = y
      rw [hf, ← he, e.apply_symm_apply, hx]
  let L : AmbientIsotopy S := {
    map := ⟨f, hfcont⟩
    homeomorphism_at := by
      intro t
      have hc : Continuous (fun y => f (t, y)) :=
        hfcont.comp (continuous_const.prodMk continuous_id)
      let e := (isHomeomorph_iff_continuous_bijective.mpr
        ⟨hc, hbij t⟩).homeomorph (fun y => f (t, y))
      exact ⟨e, fun x => rfl⟩
    at_zero := by
      intro y
      change q.projection (K.map (⟨0, by norm_num⟩, lift y)) = y
      rw [K.at_zero, hlift] }
  refine ⟨L, hf, ?_⟩
  intro t b hb
  change q.projection (K.map (t, lift b)) = b
  rw [hfix t _ (by rw [hlift]; exact hb), hlift]

theorem paired_commuting_full_preimage_transport
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    (q : BranchedDoubleCover E S) (K : AmbientIsotopy E)
    (L : AmbientIsotopy S)
    (hcomm : ∀ t x, L.map (t, q.projection x) =
      q.projection (K.map (t, x)))
    (A : Set S) :
    K.finalMap '' (q.projection ⁻¹' A) =
      q.projection ⁻¹' (L.finalMap '' A) := by
  classical
  obtain ⟨e, he⟩ := K.homeomorphism_at ⟨1, by norm_num⟩
  obtain ⟨f, hf⟩ := L.homeomorphism_at ⟨1, by norm_num⟩
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨q.projection x, hx, hcomm _ x⟩
  · rintro ⟨s, hs, heq⟩
    have hez : K.finalMap (e.symm z) = z := by
      change K.map (⟨1, by norm_num⟩, e.symm z) = z
      rw [← he, e.apply_symm_apply]
    have hp : q.projection (e.symm z) = s := by
      apply f.injective
      rw [hf, hf, hcomm]
      change q.projection (K.finalMap (e.symm z)) = L.finalMap s
      rw [hez]
      exact heq.symm
    exact ⟨e.symm z, by simpa only [Set.mem_preimage, hp] using hs, hez⟩

end CurveComplex.BranchedDoubleCover

namespace CurveComplex.HyperellipticModel
open Set Topology

theorem paired_component_projection_bijOn_transport
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    (q : BranchedDoubleCover E S)
    (K : AmbientIsotopy E) (L : AmbientIsotopy S)
    (hcomm : ∀ t x, L.map (t, q.projection x) =
      q.projection (K.map (t, x)))
    (A : Set E) (C : Set S)
    (hbij : Set.BijOn q.projection A C) :
    Set.BijOn q.projection (K.finalMap '' A) (L.finalMap '' C) := by
  obtain ⟨e, he⟩ := K.homeomorphism_at ⟨1, by norm_num⟩
  obtain ⟨f, hf⟩ := L.homeomorphism_at ⟨1, by norm_num⟩
  have hinj : Set.InjOn q.projection (K.finalMap '' A) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
    have hbase : q.projection x = q.projection y := f.injective (by
      rw [hf, hf, hcomm, hcomm]
      exact hxy)
    exact congrArg K.finalMap (hbij.injOn hx hy hbase)
  exact Set.bijOn_image_image
    (fun x => hcomm (⟨1, by norm_num⟩) x)
    hbij hinj

theorem paired_component_connected_complement_transport
    {E : Type} [TopologicalSpace E]
    (K : AmbientIsotopy E) (A : Set E)
    (hA : IsConnected Aᶜ) :
    IsConnected (K.finalMap '' A)ᶜ := by
  obtain ⟨e, he⟩ := K.homeomorphism_at ⟨1, by norm_num⟩
  have hefinal : (e : E → E) = K.finalMap := funext he
  rw [← hefinal, ← e.image_compl]
  exact e.isConnected_image.mpr hA

theorem paired_branchfixed_circle24_endpoint_transport
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) (c : Circle24 M)
    (K : AmbientIsotopy E)
    (heq : ∀ t x, K.map (t, M.cover.deck x) =
      M.cover.deck (K.map (t, x)))
    (hfix : ∀ t x, M.cover.projection x ∈ M.cover.branch →
      K.map (t, x) = x) :
    ∃ L : AmbientIsotopy S, ∃ c' : Circle24 M,
      (∀ t x, L.map (t, M.cover.projection x) =
        M.cover.projection (K.map (t, x))) ∧
      (∀ t b, b ∈ M.cover.branch → L.map (t, b) = b) ∧
      c'.val.image = L.finalMap '' c.val.image ∧
      MarkedIsotopyRel M c.val.image c'.val.image ∧
      K.finalMap '' (M.cover.projection ⁻¹' c.val.image) =
        M.cover.projection ⁻¹' c'.val.image := by
  classical
  letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
  letI : CompactSpace S := M.sphere.symm.compactSpace
  letI : T2Space S := M.sphere.symm.t2Space
  obtain ⟨L, hcomm, hmarks⟩ :=
    M.cover.paired_deck_equivariant_isotopy_descends K heq hfix
  obtain ⟨e, he⟩ := L.homeomorphism_at ⟨1, by norm_num⟩
  have hefinal : (e : S → S) = L.finalMap := funext he
  obtain ⟨c0, hc0, hsplit⟩ :=
    M.actual_marked_homeomorph_circle_transport c.val e
      (fun x hx => (he x).trans (hmarks _ x hx))
  have hc : SplitsMarked M c0 2 4 ∨ SplitsMarked M c0 4 2 :=
    c.property.elim (fun h => Or.inl (hsplit 2 4 h))
      (fun h => Or.inr (hsplit 4 2 h))
  let c' : Circle24 M := ⟨c0, hc⟩
  have himage : c'.val.image = L.finalMap '' c.val.image := by
    simpa only [c', hefinal] using hc0
  refine ⟨L, c', hcomm, hmarks, himage, ⟨L, hmarks, himage.symm⟩, ?_⟩
  rw [himage]
  exact M.cover.paired_commuting_full_preimage_transport K L hcomm c.val.image

end CurveComplex.HyperellipticModel
