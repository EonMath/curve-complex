import CurveComplexGenusTwo.Topology.LocalSurgery.LoopCircleStatement
import Mathlib

namespace CurveComplex.LocalSurgery
theorem actual_embedded_homotopic_clean_paths_produce_null_curve
    {S : Type} [TopologicalSpace S] [T2Space S]
    (b : CurveComplex.Curve S) (u z : S) (huz : u ≠ z)
    (f g : Path u z) (hf : Topology.IsEmbedding f) (hg : Topology.IsEmbedding g)
    (hgcurve : Set.range g ⊆ b.image)
    (hclean : f '' Set.Ioo (0 : CurveComplex.Interval) 1 ⊆ b.imageᶜ)
    (hhom : f.Homotopic g) :
    ∃ c : CurveComplex.Curve S,
      c.image = Set.range f ∪ Set.range g ∧
      (⟨c.map,c.embedded.continuous⟩ : C(Circle,S)).Nullhomotopic := by
  have hmeet : ∀ s t, f s = g t →
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    intro s t he
    have hb : f s ∈ b.image := he ▸ hgcurve ⟨t,rfl⟩
    by_cases hs0 : s = 0
    · left
      refine ⟨hs0, hg.injective ?_⟩
      simpa only [hs0, Path.source] using he.symm
    by_cases hs1 : s = 1
    · right
      refine ⟨hs1, hg.injective ?_⟩
      simpa only [hs1, Path.target] using he.symm
    exact (hclean ⟨s,⟨lt_of_le_of_ne s.property.1 (Ne.symm hs0),
      lt_of_le_of_ne s.property.2 hs1⟩,rfl⟩ hb).elim
  have hnull : (f.trans g.symm).Homotopic (Path.refl u) :=
    (hhom.hcomp (Path.Homotopic.refl g.symm)).trans (Path.Homotopic.trans_symm g)
  have hloopCollision : ∀ s t, (f.trans g.symm) s = (f.trans g.symm) t →
      s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
    intro s t h
    simp only [Path.trans_apply, Path.symm_apply] at h
    split_ifs at h with hs ht ht
    · left
      have he := congrArg Subtype.val (hf.injective h)
      apply Subtype.ext
      dsimp at he
      linarith
    · have he := hmeet _ _ h
      rcases he with ⟨hs0, ht0⟩ | ⟨hs1, ht1⟩
      · right; left
        constructor <;> apply Subtype.ext
        · change (s : ℝ) = 0
          have := congrArg Subtype.val hs0; dsimp at this; linarith
        · change (t : ℝ) = 1
          have := congrArg Subtype.val ht0
          simp only [unitInterval.coe_symm_eq] at this
          dsimp at this; linarith
      · exfalso
        have := congrArg Subtype.val ht1
        simp only [unitInterval.coe_symm_eq] at this
        dsimp at this; linarith
    · have he := hmeet _ _ h.symm
      rcases he with ⟨ht0, hs0⟩ | ⟨ht1, hs1⟩
      · right; right
        constructor <;> apply Subtype.ext
        · change (s : ℝ) = 1
          have := congrArg Subtype.val hs0
          simp only [unitInterval.coe_symm_eq] at this
          dsimp at this; linarith
        · change (t : ℝ) = 0
          have := congrArg Subtype.val ht0; dsimp at this; linarith
      · exfalso
        have := congrArg Subtype.val hs1
        simp only [unitInterval.coe_symm_eq] at this
        dsimp at this; linarith
    · left
      have he := congrArg Subtype.val (hg.injective h)
      apply Subtype.ext
      simp only [unitInterval.coe_symm_eq] at he
      linarith
  obtain ⟨c,hc,hcn⟩ :=
    nullhomotopic_loop_with_only_endpoint_collision_gives_curve u
      (f.trans g.symm) hloopCollision hnull
  refine ⟨c,?_,hcn⟩
  simpa only [Path.trans_range, Path.symm_range] using hc


end CurveComplex.LocalSurgery
