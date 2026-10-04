import CurveComplexGenusTwo.Dictionary.ArcEssentialDefinitions
import Mathlib.Topology.Order.IntermediateValue

namespace CurveComplex.HyperellipticModel
open Set Topology

/-- Pulling an embedded side back through another embedded interval forces
every contact with a source endpoint to be a side endpoint. -/
theorem actual_embedded_side_source_endpoint
    {X : Type} [TopologicalSpace X]
    (g f : C(Interval,X)) (hg : IsEmbedding g) (hf : IsEmbedding f)
    (hfg : range f ⊆ range g) :
    ∀ t, f t = g 0 ∨ f t = g 1 → t = 0 ∨ t = 1 := by
  let fA : C(Interval,range g) := ⟨fun t => ⟨f t,hfg ⟨t,rfl⟩⟩,
    f.continuous.subtype_mk _⟩
  let F : Interval → Interval := hg.toHomeomorph.symm ∘ fA
  have hF : Continuous F := hg.toHomeomorph.symm.continuous.comp fA.continuous
  have hFt (t : Interval) : g (F t) = f t :=
    congrArg Subtype.val (hg.toHomeomorph.apply_symm_apply (fA t))
  have hFi : Function.Injective F := by
    intro t u h
    exact hf.injective ((hFt t).symm.trans ((congrArg g h).trans (hFt u)))
  obtain hmono | hanti := hF.strictMono_of_inj_boundedOrder' hFi
  · intro t ht
    rcases ht with ht | ht
    · have hh : F t = 0 := hg.injective ((hFt t).trans ht)
      left
      by_contra hn
      have hl := hmono (lt_of_le_of_ne t.property.1 (Ne.symm hn))
      rw [hh] at hl
      exact (not_lt_of_ge (F 0).property.1) hl
    · have hh : F t = 1 := hg.injective ((hFt t).trans ht)
      right
      by_contra hn
      have hl := hmono (lt_of_le_of_ne t.property.2 hn)
      rw [hh] at hl
      exact (not_lt_of_ge (F 1).property.2) hl
  · intro t ht
    rcases ht with ht | ht
    · have hh : F t = 0 := hg.injective ((hFt t).trans ht)
      right
      by_contra hn
      have hl := hanti (lt_of_le_of_ne t.property.2 hn)
      rw [hh] at hl
      exact (not_lt_of_ge (F 1).property.1) hl
    · have hh : F t = 1 := hg.injective ((hFt t).trans ht)
      left
      by_contra hn
      have hl := hanti (lt_of_le_of_ne t.property.1 (Ne.symm hn))
      rw [hh] at hl
      exact (not_lt_of_ge (F 0).property.2) hl

#print axioms actual_embedded_side_source_endpoint
end CurveComplex.HyperellipticModel
