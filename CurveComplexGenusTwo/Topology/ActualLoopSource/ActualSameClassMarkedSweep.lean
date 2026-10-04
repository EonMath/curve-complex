import CurveComplexGenusTwo.Dictionary.ArcEssentialDefinitions

namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section

/-- The ORIGINAL same-class witness constructs an actual endpoint-fixed
sweep to the ORIGINAL target image. Loop closure is retained, not excluded. -/
theorem actual_same_class_marked_arc_sweep
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hclass : Quotient.mk (essentialArcSetoid M) a = Quotient.mk (essentialArcSetoid M) b) :
    ∃ F : C(Interval × Interval,S),
      (∀ t, F (0,t) = a.val.map t) ∧
      (∀ τ s t, F (τ,s) = F (τ,t) →
        s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) ∧
      (∀ τ, F (τ,0) = a.val.map 0 ∧ F (τ,1) = a.val.map 1) ∧
      (∀ τ t, t ≠ 0 → t ≠ 1 → F (τ,t) ∉ (M.cover.branch : Set S)) ∧
      range (fun t => F (1,t)) = b.val.image := by
  obtain ⟨H,hmarks,himage⟩ := Quotient.exact hclass
  let F : C(Interval × Interval,S) :=
    ⟨fun z => H.map (z.1,a.val.map z.2),
      H.map.continuous.comp (continuous_fst.prodMk (a.val.continuous.comp continuous_snd))⟩
  refine ⟨F,fun t => H.at_zero _,?_,?_,?_,?_⟩
  · intro τ s t he
    obtain ⟨g,hg⟩ := H.homeomorphism_at τ
    exact a.val.injective_except_loop_closure s t
      (g.injective ((hg _).trans (he.trans (hg _).symm)))
  · intro τ
    exact ⟨hmarks τ _ a.val.start_marked,hmarks τ _ a.val.end_marked⟩
  · intro τ t ht0 ht1 hm
    obtain ⟨g,hg⟩ := H.homeomorphism_at τ
    have hfix : g (F (τ,t)) = F (τ,t) := (hg _).trans (hmarks τ _ hm)
    have he : a.val.map t = F (τ,t) := g.injective ((hg _).trans hfix.symm)
    exact (a.val.marked_only_at_ends t (he.symm ▸ hm)).elim ht0 ht1
  · change range (H.finalMap ∘ a.val.map) = b.val.image
    rw [range_comp]
    exact himage

/-- Same-class sweeps lift to the actual sphere with only the two ORIGINAL
endpoints retained. The interior restriction is exported separately because
retaining endpoints in a carrier does not make interior collisions harmless. -/
theorem actual_same_class_endpoint_relative_punctured_sweep
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hclass : Quotient.mk (essentialArcSetoid M) a = Quotient.mk (essentialArcSetoid M) b) :
    ∃ F : C(Interval × Interval,
      ↑(((M.cover.branch : Set S) \ {a.val.map 0,a.val.map 1})ᶜ)),
      (∀ t, (F (0,t)).val = a.val.map t) ∧
      (∀ τ s t, (F (τ,s)).val = (F (τ,t)).val →
        s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) ∧
      (∀ τ, (F (τ,0)).val = a.val.map 0 ∧ (F (τ,1)).val = a.val.map 1) ∧
      (∀ τ t, t ≠ 0 → t ≠ 1 → (F (τ,t)).val ∉ (M.cover.branch : Set S)) ∧
      range (fun t => (F (1,t)).val) = b.val.image := by
  obtain ⟨G,h0,hcollision,hends,hmarks,himage⟩ := actual_same_class_marked_arc_sweep M a b hclass
  have havoid (z : Interval × Interval) :
      G z ∈ ((M.cover.branch : Set S) \ {a.val.map 0,a.val.map 1})ᶜ := by
    rintro ⟨hm,hnot⟩
    by_cases ht0 : z.2=0
    · exact hnot (Or.inl (ht0 ▸ (hends z.1).1))
    by_cases ht1 : z.2=1
    · exact hnot (Or.inr (mem_singleton_iff.mpr (ht1 ▸ (hends z.1).2)))
    exact hmarks z.1 z.2 ht0 ht1 hm
  exact ⟨⟨fun z => ⟨G z,havoid z⟩,G.continuous.subtype_mk _⟩,
    h0,hcollision,hends,hmarks,himage⟩
end
end CurveComplex.HyperellipticModel
