import CurveComplexGenusTwo.Topology.ActualRegionalGraphDescent.RegionalIndexedFamilyDescent

open CurveComplex Set
open scoped BigOperators

/-- A positive FULL finite contact budget yields an interior contact only after
    both anchor endpoints have been excluded. Properness pays exclusion of the
    other arc's endpoints. -/
theorem regional_positive_full_budget_interior_contact
    {S : Type} [TopologicalSpace S] {F B : Set S}
    {ι : Type} [Fintype ι]
    (anchor : C(Interval,↥F)) (a : ι → C(Interval,↥F))
    (hanchorProper : ∀ t ∈ Set.Ioo (0 : Interval) 1,
      (anchor t).val ∉ frontier F)
    (hBFront : B ⊆ frontier F)
    (haEnds : ∀ i, ((a i) 0).val ∈ B ∧ ((a i) 1).val ∈ B)
    (h0 : ∀ i, anchor 0 ∉ Set.range (a i))
    (h1 : ∀ i, anchor 1 ∉ Set.range (a i))
    (hpositive : 0 < ∑ i, (Set.range (a i) ∩ Set.range anchor).ncard) :
    ∃ (u : Interval) (i : ι) (s : Interval),
      u ∈ Set.Ioo (0 : Interval) 1 ∧ s ∈ Set.Ioo (0 : Interval) 1 ∧
      anchor u = a i s := by
  classical
  have hex : ∃ i, 0 < (Set.range (a i) ∩ Set.range anchor).ncard := by
    by_contra hn
    have hz : ∀ i, (Set.range (a i) ∩ Set.range anchor).ncard = 0 := by
      intro i
      have hi : ¬ 0 < (Set.range (a i) ∩ Set.range anchor).ncard :=
        fun hi => hn ⟨i,hi⟩
      omega
    simp only [hz,Finset.sum_const_zero] at hpositive
    omega
  obtain ⟨i,hi⟩ := hex
  obtain ⟨y,⟨s,hs⟩,u,hu⟩ := Set.nonempty_of_ncard_ne_zero (Nat.ne_of_gt hi)
  have heq : anchor u = a i s := hu.trans hs.symm
  have hu0 : u ≠ 0 := by
    intro h
    exact h0 i ⟨s,heq.symm.trans (congrArg anchor h)⟩
  have hu1 : u ≠ 1 := by
    intro h
    exact h1 i ⟨s,heq.symm.trans (congrArg anchor h)⟩
  have hui : u ∈ Set.Ioo (0 : Interval) 1 :=
    ⟨lt_of_le_of_ne (unitInterval.nonneg' (t := u)) hu0.symm,
      lt_of_le_of_ne (unitInterval.le_one u) hu1⟩
  have hs0 : s ≠ 0 := by
    intro h
    have hb : (anchor u).val ∈ frontier F := by
      rw [heq,h]
      exact hBFront (haEnds i).1
    exact hanchorProper u hui hb
  have hs1 : s ≠ 1 := by
    intro h
    have hb : (anchor u).val ∈ frontier F := by
      rw [heq,h]
      exact hBFront (haEnds i).2
    exact hanchorProper u hui hb
  exact ⟨u,i,s,hui,⟨lt_of_le_of_ne (unitInterval.nonneg' (t := s)) hs0.symm,
    lt_of_le_of_ne (unitInterval.le_one s) hs1⟩,heq⟩

#print axioms regional_positive_full_budget_interior_contact
