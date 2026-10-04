import CurveComplexGenusTwo.Dictionary.BranchedCover
import CurveComplexGenusTwo.Foundations.Definitions

namespace CurveComplex.BranchedDoubleCover

/-- An actual deck-invariant embedded interval meets the ramification locus.
This is the interval fixed-point obstruction used in source Lemma 4.5. -/
theorem invariant_embedded_interval_meets_branch
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    (q : BranchedDoubleCover E S) (α : C(Interval,E))
    (hα : Topology.IsEmbedding α)
    (hinv : q.deck '' Set.range α ⊆ Set.range α) :
    ∃ t : Interval, q.projection (α t) ∈ q.branch := by
  let e : Interval ≃ₜ Set.range α := hα.toHomeomorph
  let g : C(Interval,Interval) :=
    ⟨fun t => e.symm ⟨q.deck (α t),hinv ⟨α t,⟨t,rfl⟩,rfl⟩⟩,
      e.symm.continuous.comp ((q.deck.continuous.comp α.continuous).subtype_mk _)⟩
  have hg (t : Interval) : α (g t) = q.deck (α t) := by
    exact congrArg Subtype.val (e.apply_symm_apply _)
  let f : Interval → ℝ := fun t => (g t).val - t.val
  have hf : Continuous f :=
    (continuous_subtype_val.comp g.continuous).sub continuous_subtype_val
  have hf0 : 0 ≤ f 0 := by simpa [f] using (g 0).property.1
  have hf1 : f 1 ≤ 0 := by
    dsimp [f]
    exact sub_nonpos.mpr (g 1).property.2
  obtain ⟨t,_,ht⟩ := intermediate_value_Icc' (by norm_num : (0 : Interval) ≤ 1)
    hf.continuousOn (show (0 : ℝ) ∈ Set.Icc (f 1) (f 0) from ⟨hf1,hf0⟩)
  have hgt : g t = t := by
    apply Subtype.ext
    exact sub_eq_zero.mp ht
  refine ⟨t,(q.fixed_iff_branch (α t)).mp ?_⟩
  rw [← hg t,hgt]

theorem unramified_embedded_interval_not_deck_invariant
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    (q : BranchedDoubleCover E S) (α : C(Interval,E))
    (hα : Topology.IsEmbedding α)
    (hfree : ∀ t, q.projection (α t) ∉ q.branch) :
    ¬ q.deck '' Set.range α ⊆ Set.range α := by
  intro h
  obtain ⟨t,ht⟩ := q.invariant_embedded_interval_meets_branch α hα h
  exact hfree t ht

end CurveComplex.BranchedDoubleCover
