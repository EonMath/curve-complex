import CurveComplexGenusTwo.Topology.ActualRegionalAllCrossing.RegionalCrossingFNullFromCover
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.FreeBoundaryNullGeometry

namespace CoherentEndpointMotion.FreeBoundaryContactRepair
open CurveComplex Set Topology Schoenflies RegionalEmbeddedFamily FreeBoundaryNullGeometry

/-- Proper arcs with disjoint unordered endpoint sets can meet only in their
strict interiors, and every such contact is off the literal boundary. -/
theorem free_boundary_contact_parameters_interior
    {X : Type} [TopologicalSpace X] (B : Set X) (a b : C(Interval,X))
    (hends : a 0 ∈ B ∧ a 1 ∈ B ∧ b 0 ∈ B ∧ b 1 ∈ B)
    (hproper : ∀ t ∈ Ioo (0 : Interval) 1, a t ∉ B ∧ b t ∉ B)
    (hdis : Disjoint ({a 0,a 1} : Set X) {b 0,b 1})
    (s t : Interval) (hst : a s = b t) :
    s ∈ Ioo (0 : Interval) 1 ∧ t ∈ Ioo (0 : Interval) 1 ∧ a s ∉ B := by
  have boundary_end (c : C(Interval,X))
      (hi : ∀ u ∈ Ioo (0 : Interval) 1, c u ∉ B) (u : Interval)
      (hu : c u ∈ B) : u = 0 ∨ u = 1 := by
    by_cases h0 : u = 0
    · exact Or.inl h0
    by_cases h1 : u = 1
    · exact Or.inr h1
    exact False.elim (hi u ⟨lt_of_le_of_ne u.property.1 (Ne.symm h0),
      lt_of_le_of_ne u.property.2 h1⟩ hu)
  have hoff : a s ∉ B := by
    intro hsB
    have hs := boundary_end a (fun u hu => (hproper u hu).1) s hsB
    have ht := boundary_end b (fun u hu => (hproper u hu).2) t (hst ▸ hsB)
    have hsa : a s ∈ ({a 0,a 1} : Set X) := hs.elim (fun h => Or.inl (h ▸ rfl))
      (fun h => Or.inr (h ▸ rfl))
    have htb : b t ∈ ({b 0,b 1} : Set X) := ht.elim (fun h => Or.inl (h ▸ rfl))
      (fun h => Or.inr (h ▸ rfl))
    exact Set.disjoint_left.mp hdis hsa (hst ▸ htb)
  have hs0 : s ≠ 0 := fun he => hoff (he ▸ hends.1)
  have hs1 : s ≠ 1 := fun he => hoff (he ▸ hends.2.1)
  have ht0 : t ≠ 0 := fun he => hoff (hst ▸ (he ▸ hends.2.2.1))
  have ht1 : t ≠ 1 := fun he => hoff (hst ▸ (he ▸ hends.2.2.2))
  exact ⟨⟨lt_of_le_of_ne s.property.1 (Ne.symm hs0),lt_of_le_of_ne s.property.2 hs1⟩,
    ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩,hoff⟩

end CoherentEndpointMotion.FreeBoundaryContactRepair
