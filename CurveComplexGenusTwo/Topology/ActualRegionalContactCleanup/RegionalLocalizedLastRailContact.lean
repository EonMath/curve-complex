import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches

open CurveComplex Set Topology

theorem regional_cleanup_contact_containment_strict_drop
    {S : Type} [TopologicalSpace S] {F : Set S}
    (anchor old b : C(Interval,↥F)) (r s : Interval)
    (hcontact : anchor r = old s)
    (hfinite : (Set.range old ∩ Set.range anchor).Finite)
    (hcontain : Set.range b ∩ Set.range anchor ⊆
      (Set.range old ∩ Set.range anchor) \ {old s}) :
    (Set.range b ∩ Set.range anchor).Finite ∧
    (Set.range b ∩ Set.range anchor).ncard <
      (Set.range old ∩ Set.range anchor).ncard := by
  have hsub : Set.range b ∩ Set.range anchor ⊆
      Set.range old ∩ Set.range anchor := fun y hy => (hcontain hy).1
  refine ⟨hfinite.subset hsub,Set.ncard_lt_ncard ?_ hfinite⟩
  apply Set.ssubset_iff_subset_ne.mpr
  refine ⟨hsub,?_⟩
  intro heq
  have hp : old s ∈ Set.range b ∩ Set.range anchor :=
    heq.symm ▸ ⟨Set.mem_range_self s,⟨r,hcontact⟩⟩
  exact (hcontain hp).2 (Set.mem_singleton _)

#print axioms regional_cleanup_contact_containment_strict_drop
