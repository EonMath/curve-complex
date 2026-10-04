import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches

open CurveComplex Set Topology

theorem regional_F_raw_branch_range_transports_to_Q
    {S : Type} [TopologicalSpace S]
    (F Q : Set S) (hFQ : F ⊆ Q)
    (aF bF dF : C(Interval,↥F))
    (aQ bQ dQ : C(Interval,↥Q))
    (ha : ∀ t, (aF t).val = (aQ t).val)
    (hb : ∀ t, (bF t).val = (bQ t).val)
    (hd : ∀ t, (dF t).val = (dQ t).val)
    (r u : Interval) (right : Bool)
    (hrange : Set.range dF =
      (aF '' Set.Icc 0 r) ∪
      (bF '' (if right then Set.Icc u 1 else Set.Icc 0 u))) :
    Set.range dQ =
      (aQ '' Set.Icc 0 r) ∪
      (bQ '' (if right then Set.Icc u 1 else Set.Icc 0 u)) := by
  let i : ↥F → ↥Q := fun y => ⟨y.val,hFQ y.property⟩
  have image_eq (pF : C(Interval,↥F)) (pQ : C(Interval,↥Q))
      (hp : ∀ t, (pF t).val = (pQ t).val) (A : Set Interval) :
      pQ '' A = i '' (pF '' A) := by
    ext y
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨pF t,⟨t,ht,rfl⟩,Subtype.ext (hp t)⟩
    · rintro ⟨z,⟨t,ht,rfl⟩,rfl⟩
      exact ⟨t,ht,Subtype.ext (hp t).symm⟩
  have hD : Set.range dQ = i '' Set.range dF := by
    simpa only [Set.image_univ] using
      image_eq dF dQ hd Set.univ
  rw [hD,hrange,Set.image_union]
  rw [← image_eq aF aQ ha (Set.Icc 0 r),
    ← image_eq bF bQ hb (if right then Set.Icc u 1 else Set.Icc 0 u)]

#print axioms regional_F_raw_branch_range_transports_to_Q
