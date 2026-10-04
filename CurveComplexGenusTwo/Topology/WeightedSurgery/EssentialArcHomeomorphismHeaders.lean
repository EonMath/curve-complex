import CurveComplexGenusTwo.Topology.WeightedSurgery.ArcSurgeryProducers

namespace CurveComplex.HyperellipticModel.ArcSurgery

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/- Actual loop essentiality survives marked homeomorphisms by transporting
maximal connected complementary components, rather than assuming it. -/
theorem essentialMarkedArc_of_mark_fixed_homeomorph (M : HyperellipticModel E S) (h : S ≃ₜ S)
    (hfix : ∀ p, p ∈ M.cover.branch → h p = p)
    (a b : MarkedArc M) (hb : ∀ r, b.map r = h (a.map r))
    (ha : IsEssentialMarkedArc M a) : IsEssentialMarkedArc M b := by
  have himage : b.image = h '' a.image := by
    ext p
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨a.map r, ⟨r, rfl⟩, (hb r).symm⟩
    · rintro ⟨q, ⟨r, rfl⟩, rfl⟩
      exact ⟨r, hb r⟩
  rcases ha with ha | ha
  · left
    change a.map ⟨0, by norm_num⟩ ≠ a.map ⟨1, by norm_num⟩ at ha
    change b.map ⟨0, by norm_num⟩ ≠ b.map ⟨1, by norm_num⟩
    intro he
    apply ha
    apply h.injective
    rw [← hb, ← hb]
    exact he
  · right
    intro U hU
    rw [himage] at hU
    have hpull : IsComplementComponent a.image (h.symm '' U) := by
      refine ⟨hU.1.image h.symm, hU.2.1.image h.symm h.symm.continuous.continuousOn, ?_, ?_⟩
      · rintro p ⟨q, hq, rfl⟩ hp
        apply hU.2.2.1 hq
        exact ⟨h.symm q, hp, h.apply_symm_apply q⟩
      · intro V hV hUV hVa
        have hu : U ⊆ h '' V := by
          intro q hq
          exact ⟨h.symm q, hUV ⟨q, hq, rfl⟩, h.apply_symm_apply q⟩
        have hv : h '' V ⊆ (h '' a.image)ᶜ := by
          rintro q ⟨p, hp, rfl⟩ ⟨r, hr, he⟩
          exact hVa hp (h.injective he ▸ hr)
        have heq : h '' V = U :=
          hU.2.2.2 (h '' V) (hV.image h h.continuous.continuousOn) hu hv
        apply Set.Subset.antisymm
        · intro p hp
          have hh : h p ∈ U := heq ▸ (Set.mem_image_of_mem h hp)
          exact ⟨h p, hh, h.symm_apply_apply p⟩
        · exact hUV
    obtain ⟨p, hp, q, hq, he⟩ := ha (h.symm '' U) hpull
    have heq : q = h p := by
      simpa only [h.apply_symm_apply] using congrArg h he
    rw [hfix p hp] at heq
    exact ⟨p, hp, heq ▸ hq⟩

end CurveComplex.HyperellipticModel.ArcSurgery
