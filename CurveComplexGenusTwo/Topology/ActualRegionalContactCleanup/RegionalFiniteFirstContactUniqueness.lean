import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches

open CurveComplex Set Topology

theorem regional_finite_first_contact_selected_prefix_unique
    {S : Type} [TopologicalSpace S] {F : Set S}
    {ι : Type} [Fintype ι]
    (anchor : C(Interval,↥F)) (a : ι → C(Interval,↥F))
    (haEmb : ∀ i, Topology.IsEmbedding (a i))
    (r s : Interval) (k : ι) (hcontact : anchor r = a k s)
    (hclear : ∀ i u, u < r → anchor u ∉ Set.range (a i)) :
    ∀ v t : Interval, t ≤ r → a k v = anchor t → v = s ∧ t = r := by
  intro v t htr he
  have hte : t = r := by
    rcases htr.eq_or_lt with heq | hlt
    · exact heq
    · exact False.elim (hclear k t hlt ⟨v,he⟩)
  subst t
  refine ⟨(haEmb k).injective ?_,rfl⟩
  exact he.trans hcontact

#print axioms regional_finite_first_contact_selected_prefix_unique
