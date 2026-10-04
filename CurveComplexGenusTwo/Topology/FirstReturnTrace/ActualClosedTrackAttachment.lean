import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualEmbeddedArcConcatenation
import CurveComplexGenusTwo.Dictionary.ArcPreimageClosed
namespace CurveComplex
open Set Topology

/-- Construct an ACTUAL embedded closed source curve from two embedded tracks
and two embedded corner connectors with their exact geometric incidences.
The resulting Curve has the exact union image of the four source pieces. -/
theorem source_closed_curve_of_tracks_and_connectors
    {S : Type} [TopologicalSpace S] [T2Space S]
    (f g c₀ c₁ : C(Interval,S))
    (hf : IsEmbedding f) (hg : IsEmbedding g)
    (hc₀ : IsEmbedding c₀) (hc₁ : IsEmbedding c₁)
    (h₀f : c₀ 0 = f 0) (h₀g : c₀ 1 = g 0)
    (h₁f : c₁ 0 = f 1) (h₁g : c₁ 1 = g 1)
    (h₀fmeet : Set.range c₀ ∩ Set.range f = {f 0})
    (h₁fmeet : Set.range f ∩ Set.range c₁ = {f 1})
    (h₀gmeet : Set.range c₀ ∩ Set.range g = {g 0})
    (h₁gmeet : Set.range c₁ ∩ Set.range g = {g 1})
    (hfg : Disjoint (Set.range f) (Set.range g))
    (hcc : Disjoint (Set.range c₀) (Set.range c₁)) :
    ∃ d : Curve S,
      d.image = (Set.range f ∪ Set.range g) ∪ (Set.range c₀ ∪ Set.range c₁) := by
  let rev : C(Interval,Interval) := ⟨unitInterval.symmHomeomorph,
    unitInterval.symmHomeomorph.continuous⟩
  let r : C(Interval,S) := c₀.comp rev
  have hr : IsEmbedding r := hc₀.comp unitInterval.symmHomeomorph.isEmbedding
  have hrange : Set.range r = Set.range c₀ :=
    unitInterval.symmHomeomorph.surjective.range_comp c₀
  have hr0 : r 0 = g 0 := by simpa [r,rev] using h₀g
  have hr1 : r 1 = f 0 := by simpa [r,rev] using h₀f
  have hrmeet : Set.range r ∩ Set.range f = {r 1} := by
    rw [hrange,h₀fmeet,hr1]
  obtain ⟨h,hh,hh0,hh1,hhrange⟩ := source_embedded_arc_concatenation r f hr hf hr1 hrmeet
  have hhmeet : Set.range h ∩ Set.range c₁ = {h 1} := by
    rw [hhrange,hrange,Set.union_inter_distrib_right,
      Set.disjoint_iff_inter_eq_empty.mp hcc,h₁fmeet,Set.empty_union,hh1]
  obtain ⟨H,hH,hH0,hH1,hHrange⟩ := source_embedded_arc_concatenation h c₁ hh hc₁
    (hh1.trans h₁f.symm) hhmeet
  have hHstart : H 0 = g 0 := hH0.trans (hh0.trans hr0)
  have hHfinish : H 1 = g 1 := hH1.trans h₁g
  have hHgrange : Set.range H ∩ Set.range g = {g 0,g 1} := by
    rw [hHrange,hhrange,hrange,Set.union_inter_distrib_right,
      Set.union_inter_distrib_right,h₀gmeet,
      Set.disjoint_iff_inter_eq_empty.mp hfg,h₁gmeet,Set.union_empty]
    rfl
  have hcollision (s t : Interval) (he : H s = g t) :
      (s=0 ∧ t=0) ∨ (s=1 ∧ t=1) := by
    have hp : H s ∈ Set.range H ∩ Set.range g :=
      ⟨Set.mem_range_self _,⟨t,he.symm⟩⟩
    rw [hHgrange] at hp
    rcases hp with hp | hp
    · have hp' : H s = g 0 := hp
      exact Or.inl ⟨hH.injective (hp'.trans hHstart.symm),hg.injective (he.symm.trans hp')⟩
    · have hp' : H s = g 1 := Set.mem_singleton_iff.mp hp
      exact Or.inr ⟨hH.injective (hp'.trans hHfinish.symm),hg.injective (he.symm.trans hp')⟩
  obtain ⟨d,hd⟩ := exists_curve_of_two_arcs H g hH.injective hg.injective hHstart hHfinish hcollision
  refine ⟨d,?_⟩
  rw [hd,hHrange,hhrange,hrange]
  ext x
  simp only [Set.mem_union]
  tauto
end CurveComplex
#print axioms CurveComplex.source_closed_curve_of_tracks_and_connectors
