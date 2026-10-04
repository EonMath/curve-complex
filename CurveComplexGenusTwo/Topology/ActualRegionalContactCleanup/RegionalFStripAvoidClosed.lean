import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches

open CurveComplex Set Topology

theorem regional_proper_F_strip_narrow_into_open
    {S : Type} [TopologicalSpace S] [T2Space S]
    (F B : Set S) (a : C(Interval,↥F))
    (E : C(Interval × Set.Icc (-1 : ℝ) 1,↥F))
    (hE : Topology.IsEmbedding E)
    (hcenter : ∀ t, E (t,⟨0,by norm_num⟩) = a t)
    (hend : ∀ w, (E (0,w)).val ∈ B ∧ (E (1,w)).val ∈ B)
    (hint : ∀ t ∈ Set.Ioo (0 : Interval) 1, ∀ w,
      (E (t,w)).val ∈ interior F)
    (hopen : IsOpen (E '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}))
    (U : Set ↥F) (hU : IsOpen U) (haU : Set.range a ⊆ U) :
    ∃ N : C(Interval × Set.Icc (-1 : ℝ) 1,↥F),
      Topology.IsEmbedding N ∧
      Set.range N ⊆ U ∧
      (∀ t, N (t,⟨0,by norm_num⟩) = a t) ∧
      (∀ w, (N (0,w)).val ∈ B ∧ (N (1,w)).val ∈ B) ∧
      (∀ t ∈ Set.Ioo (0 : Interval) 1, ∀ w,
        (N (t,w)).val ∈ interior F) ∧
      IsOpen (N '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}) := by
  obtain ⟨ρ,hρ,n,hn,hnU,hnformula,hncenter⟩ :=
    source_shrink_embedded_strip_in_open E hE U hU
      (fun t => by rw [hcenter]; exact haU (Set.mem_range_self t))
  let N : C(Interval × Set.Icc (-1 : ℝ) 1,↥F) := ⟨n,hn.continuous⟩
  have hNopen : IsOpen (N '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}) :=
    regional_strip_narrow_open_core F F (Set.Subset.rfl) E hE hopen
      ρ hρ.1 hρ.2 N (fun z => congrArg Subtype.val (hnformula z))
  refine ⟨N,hn,hnU,?_,?_,?_,hNopen⟩
  · intro t
    exact (hncenter t).trans (hcenter t)
  · intro w
    change (n (0,w)).val ∈ B ∧ (n (1,w)).val ∈ B
    rw [hnformula,hnformula]
    exact hend _
  · intro t ht w
    change (n (t,w)).val ∈ interior F
    rw [hnformula]
    exact hint t ht _

#print axioms regional_proper_F_strip_narrow_into_open
