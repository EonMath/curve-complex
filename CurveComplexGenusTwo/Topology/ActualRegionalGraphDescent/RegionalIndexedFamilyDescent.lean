import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalFiniteFullContactCommonStep

open CurveComplex Set
open scoped BigOperators

/-- Replacing one representative by a retained-family-clear branch preserves
    literal pairwise disjointness, even if quotient labels coincide. -/
theorem regional_indexed_representative_update_full_budget
    {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]
    (a : ι → C(Interval,X)) (anchor b : C(Interval,X)) (k : ι)
    (hdrop : (Set.range b ∩ Set.range anchor).ncard <
      (Set.range (a k) ∩ Set.range anchor).ncard) :
    (∑ i, (Set.range (Function.update a k b i) ∩ Set.range anchor).ncard) <
      ∑ i, (Set.range (a i) ∩ Set.range anchor).ncard := by
  apply Finset.sum_lt_sum
  · intro i hi
    by_cases hik : i = k
    · subst i
      simpa using hdrop.le
    · simp [Function.update,hik]
  · exact ⟨k,Finset.mem_univ _,by simpa using hdrop⟩



theorem regional_cleanup_contact_containment_preserves_anchor_endpoints
    {X : Type} [TopologicalSpace X]
    (anchor old b : C(Interval,X)) (s : Interval)
    (hcontain : Set.range b ∩ Set.range anchor ⊆
      (Set.range old ∩ Set.range anchor) \ {old s})
    (h0 : anchor 0 ∉ Set.range old) (h1 : anchor 1 ∉ Set.range old) :
    anchor 0 ∉ Set.range b ∧ anchor 1 ∉ Set.range b := by
  constructor
  · intro hb
    exact h0 (hcontain ⟨hb,Set.mem_range_self 0⟩).1.1
  · intro hb
    exact h1 (hcontain ⟨hb,Set.mem_range_self 1⟩).1.1



theorem regional_zero_full_budget_disjoint
    {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι]
    (a : ι → C(Interval,X)) (anchor : C(Interval,X))
    (hfinite : ∀ i, (Set.range (a i) ∩ Set.range anchor).Finite)
    (hzero : (∑ i, (Set.range (a i) ∩ Set.range anchor).ncard) = 0) :
    ∀ i, Disjoint (Set.range (a i)) (Set.range anchor) := by
  intro i
  have hi : (Set.range (a i) ∩ Set.range anchor).ncard = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i hi => Nat.zero_le _)).mp hzero i
      (Finset.mem_univ _)
  exact Set.disjoint_iff_inter_eq_empty.mpr ((Set.ncard_eq_zero (hfinite i)).mp hi)



theorem regional_indexed_graph_update_disjoint
    {X : Type} [TopologicalSpace X] {ι : Type} [DecidableEq ι]
    (adjacent : ι → ι → Prop)
    (hsymm : ∀ i j, adjacent i j → adjacent j i)
    (hirrefl : ∀ i, ¬ adjacent i i)
    (a : ι → C(Interval,X)) (k : ι) (b : C(Interval,X))
    (ha : ∀ i j, adjacent i j → Disjoint (Set.range (a i)) (Set.range (a j)))
    (hb : ∀ i, adjacent k i → Disjoint (Set.range b) (Set.range (a i))) :
    ∀ i j, adjacent i j → Disjoint
      (Set.range (Function.update a k b i))
      (Set.range (Function.update a k b j)) := by
  intro i j hij
  have hne : i ≠ j := fun he => hirrefl j (he ▸ hij)
  by_cases hik : i = k
  · subst i
    simpa [Function.update,hne.symm] using hb j hij
  · by_cases hjk : j = k
    · subst j
      simpa [Function.update,hik] using (hb i (hsymm i k hij)).symm
    · simpa [Function.update,hik,hjk] using ha i j hij



theorem regional_indexed_update_contact_invariants
    {X : Type} [TopologicalSpace X] {ι : Type} [DecidableEq ι]
    (a : ι → C(Interval,X)) (anchor b : C(Interval,X)) (k : ι) (s : Interval)
    (hfinite : ∀ i, (Set.range (a i) ∩ Set.range anchor).Finite)
    (h0 : ∀ i, anchor 0 ∉ Set.range (a i))
    (h1 : ∀ i, anchor 1 ∉ Set.range (a i))
    (hcontain : Set.range b ∩ Set.range anchor ⊆
      (Set.range (a k) ∩ Set.range anchor) \ {a k s}) :
    (∀ i, (Set.range (Function.update a k b i) ∩ Set.range anchor).Finite) ∧
    (∀ i, anchor 0 ∉ Set.range (Function.update a k b i)) ∧
    (∀ i, anchor 1 ∉ Set.range (Function.update a k b i)) := by
  have hf : (Set.range b ∩ Set.range anchor).Finite :=
    (hfinite k).subset (fun y hy => (hcontain hy).1)
  have hend := regional_cleanup_contact_containment_preserves_anchor_endpoints
    anchor (a k) b s hcontain (h0 k) (h1 k)
  refine ⟨?_,?_,?_⟩
  · intro i
    by_cases hi : i = k
    · simpa [hi] using hf
    · simpa [Function.update,hi] using hfinite i
  · intro i
    by_cases hi : i = k
    · simpa [hi] using hend.1
    · simpa [Function.update,hi] using h0 i
  · intro i
    by_cases hi : i = k
    · simpa [hi] using hend.2
    · simpa [Function.update,hi] using h1 i


