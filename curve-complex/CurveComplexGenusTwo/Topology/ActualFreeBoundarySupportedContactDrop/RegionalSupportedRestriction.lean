import CurveComplexGenusTwo.Foundations.Definitions

open CurveComplex Set Topology

theorem regional_ambient_isotopy_restricts_with_support
    {S : Type} [TopologicalSpace S] (F U : Set S)
    (hU : U ⊆ interior F) (H : AmbientIsotopy S)
    (hfix : ∀ t y, y ∉ U → H.map (t, y) = y) :
    ∃ K : AmbientIsotopy ↥F,
      (∀ t y, (K.map (t, y)).val = H.map (t, y.val)) ∧
      (∀ t y, y.val ∉ U → K.map (t, y) = y) ∧
      ∀ t y, y.val ∈ frontier F → K.map (t, y) = y := by
  have hinj (t : Interval) : Function.Injective (fun y => H.map (t, y)) := by
    obtain ⟨h, hh⟩ := H.homeomorphism_at t
    intro y z he
    exact h.injective (by simpa only [hh] using he)
  have hfixF : ∀ t y, y ∉ F → H.map (t, y) = y := by
    intro t y hy
    exact hfix t y (fun hz => hy (interior_subset (hU hz)))
  have hmem (t : Interval) (y : S) : H.map (t, y) ∈ F ↔ y ∈ F := by
    constructor
    · intro hy
      by_contra hn
      rw [hfixF t y hn] at hy
      exact hn hy
    · intro hy
      by_contra hn
      have he : H.map (t, H.map (t, y)) = H.map (t, y) := hfixF t _ hn
      have hey : H.map (t, y) = y := hinj t he
      exact hn (hey.symm ▸ hy)
  let K : AmbientIsotopy ↥F := {
    map := ⟨fun z => ⟨H.map (z.1, z.2.val),
      (hmem z.1 z.2.val).mpr z.2.property⟩,
      (H.map.continuous.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _⟩
    homeomorphism_at := by
      intro t
      obtain ⟨h, hh⟩ := H.homeomorphism_at t
      let k : ↥F ≃ₜ ↥F := h.subtype (fun y => by
        rw [hh]
        exact (hmem t y).symm)
      refine ⟨k, ?_⟩
      intro y
      apply Subtype.ext
      exact hh y.val
    at_zero := by
      intro y
      apply Subtype.ext
      exact H.at_zero y.val }
  have hK (t : Interval) (y : ↥F) :
      (K.map (t, y)).val = H.map (t, y.val) := rfl
  refine ⟨K, hK, ?_, ?_⟩
  · intro t y hy
    apply Subtype.ext
    rw [hK]
    exact hfix t y.val hy
  · intro t y hy
    apply Subtype.ext
    rw [hK]
    exact hfix t y.val (fun hz =>
      Set.disjoint_left.mp disjoint_interior_frontier (hU hz) hy)
