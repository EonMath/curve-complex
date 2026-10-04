import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualFacingSideUniquenessLocal
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies

-- The actual cylinder and its derived exterior sides discharge the collar port.
example {X : Type} [TopologicalSpace X] [T2Space X]
    (q : C(Circle × Interval,X)) (C D V Z : Set X)
    (hq0 : Set.range (fun z => q (z,0))=C)
    (hq1 : Set.range (fun z => q (z,1))=D)
    (hmid : IsOpen (q '' {p : Circle × Interval | 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1}))
    (hclV : closure V=V ∪ C) (hclZ : closure Z=Z ∪ D)
    (hqV : Disjoint (Set.range q) V) (hqZ : Disjoint (Set.range q) Z) :
    frontier (Set.range q)=C ∪ D := by
  audit_main14_base3
    have hclosed : IsClosed (Set.range q) := (isCompact_range q.continuous).isClosed
    have hiV : Disjoint (interior (Set.range q)) (closure V) :=
      (hqV.mono_left interior_subset).closure_right isOpen_interior
    have hiZ : Disjoint (interior (Set.range q)) (closure Z) :=
      (hqZ.mono_left interior_subset).closure_right isOpen_interior
    apply Set.Subset.antisymm
    · intro x hx
      have hxq : x ∈ Set.range q := hclosed.closure_eq ▸ frontier_subset_closure hx
      obtain ⟨⟨z,t⟩,rfl⟩ := hxq
      by_cases ht0 : t=0
      · subst t
        exact Or.inl (hq0 ▸ Set.mem_range_self z)
      by_cases ht1 : t=1
      · subst t
        exact Or.inr (hq1 ▸ Set.mem_range_self z)
      have ht0' : 0 < (t:ℝ) := lt_of_le_of_ne t.property.1
        (fun he => ht0 (Subtype.ext he.symm))
      have ht1' : (t:ℝ)<1 := lt_of_le_of_ne t.property.2
        (fun he => ht1 (Subtype.ext he))
      have hmem : q (z,t) ∈ q '' {p : Circle × Interval | 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1} :=
        ⟨(z,t),⟨ht0',ht1'⟩,rfl⟩
      have hsub : q '' {p : Circle × Interval | 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1} ⊆ Set.range q :=
        Set.image_subset_range _ _
      have hin := interior_maximal hsub hmid hmem
      exact False.elim (Set.disjoint_left.mp disjoint_interior_frontier hin hx)
    · intro x hx
      rw [frontier,hclosed.closure_eq]
      refine ⟨?_,?_⟩
      · rcases hx with hc | hd
        · obtain ⟨z,rfl⟩ := hq0.symm ▸ hc
          exact Set.mem_range_self (z,0)
        · obtain ⟨z,rfl⟩ := hq1.symm ▸ hd
          exact Set.mem_range_self (z,1)
      · intro hi
        rcases hx with hc | hd
        · exact Set.disjoint_left.mp hiV hi (hclV.symm ▸ Or.inr hc)
        · exact Set.disjoint_left.mp hiZ hi (hclZ.symm ▸ Or.inr hd)
end CurveComplex.HyperellipticModel
