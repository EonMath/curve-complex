import CurveComplexGenusTwo.Foundations.ActualIntersectionBridge

namespace CurveComplex.LocalSurgery

/-- Apply an actual ambient homeomorphism to an embedded curve. -/
noncomputable def homeomorphCurve
    {S : Type*} [TopologicalSpace S] (e : S ≃ₜ S) (a : Curve S) : Curve S :=
  ⟨e ∘ a.map, e.isEmbedding.comp a.embedded⟩

/-- Simultaneous homeomorphism transport preserves actual local crossings
and the exact finite cardinality, not only parity. -/
theorem transverse_homeomorph_count
    {S : Type*} [TopologicalSpace S]
    (e : S ≃ₜ S) (a b : Curve S) (hab : Transverse a b) :
    ∃ ht : Transverse (homeomorphCurve e a) (homeomorphCurve e b),
      ht.1.toFinset.card = hab.1.toFinset.card := by
  classical
  have himage (c : Curve S) : (homeomorphCurve e c).image = e '' c.image :=
    Set.range_comp e c.map
  have hinter : (homeomorphCurve e a).image ∩ (homeomorphCurve e b).image =
      e '' (a.image ∩ b.image) := by
    rw [himage, himage, Set.image_inter e.injective]
  have hfinite : ((homeomorphCurve e a).image ∩
      (homeomorphCurve e b).image).Finite := by
    rw [hinter]
    exact hab.1.image e
  have htrans : Transverse (homeomorphCurve e a) (homeomorphCurve e b) := by
    refine ⟨hfinite, ?_⟩
    intro q hq
    rw [hinter] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    obtain ⟨U, V, hpU, h, hU, hV, hzero, haxes⟩ := hab.2 p hp
    let eU := e.image U
    let hpU' : e p ∈ e '' U := Set.mem_image_of_mem e hpU
    let h' := eU.symm.trans h
    refine ⟨e '' U, V, hpU', h', e.isOpenMap U hU, hV, ?_, ?_⟩
    · have heU : eU.symm ⟨e p, hpU'⟩ = ⟨p, hpU⟩ := by
        apply Subtype.ext
        exact e.symm_apply_apply p
      simpa only [h', Homeomorph.trans_apply, heU] using hzero
    · intro x hx
      let y := eU.symm ⟨x, hx⟩
      have hy : (y : S) = e.symm x := rfl
      have hmem (c : Curve S) :
          x ∈ (homeomorphCurve e c).image ↔ (y : S) ∈ c.image := by
        rw [himage, hy]
        exact Set.mem_image_iff_of_inverse e.symm_apply_apply e.apply_symm_apply
      rcases haxes (y : S) y.property with ⟨ha, hb⟩
      constructor
      · exact (hmem a).trans ha
      · exact (hmem b).trans hb
  refine ⟨htrans, ?_⟩
  rw [← Set.ncard_eq_toFinset_card _ htrans.1,
    ← Set.ncard_eq_toFinset_card _ hab.1, hinter]
  exact Set.ncard_image_of_injective _ e.injective

end CurveComplex.LocalSurgery
