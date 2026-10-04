import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalRawBranchParameterSplit
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalTaperedProfileClearance

open CurveComplex Set Topology

/-- The branch has a cutoff beyond its corner before any subsequent remaining
    anchor contact. Its tail past the cutoff stays on old and misses the corner. -/
theorem regional_raw_branch_tail_cutoff
    {S : Type} [TopologicalSpace S] [T2Space S] {F : Set S}
    (anchor old : C(Interval,↥F)) (ha : Topology.IsEmbedding anchor)
    (r s : Interval) (hcontact : anchor r = old s) (right : Bool)
    (hb : Topology.IsEmbedding (regionalRawSurgeryBranch anchor old r s hcontact right))
    (hfinite : (Set.range old ∩ Set.range anchor).Finite) :
    ∃ q : Interval, (1/2 : ℝ) < q ∧ q < (1 : Interval) ∧
      (∀ t ∈ Set.Icc (0 : Interval) q,
        regionalRawSurgeryBranch anchor old r s hcontact right t ∈
          anchor '' Set.Icc r 1 → (t : ℝ) = 1/2) ∧
      ∀ t : Interval, q ≤ t →
        regionalRawSurgeryBranch anchor old r s hcontact right t ∈
          Set.range old \ {old s} := by
  let a := regionalRawSurgeryBranch anchor old r s hcontact right
  let c : Interval := ⟨1/2,by norm_num⟩
  have hc : a c = old s := regionalRawSurgeryBranch_half_contact anchor old r s hcontact right
  have hcK : a c ∈ anchor '' Set.Icc r 1 :=
    ⟨r,⟨le_refl _,r.property.2⟩,hcontact.trans hc.symm⟩
  have hfin := regionalRawSurgeryBranch_remaining_anchor_contacts_finite
    anchor old ha r s hcontact right hfinite
  obtain ⟨l,u,hlc,hcu,hgap⟩ := regional_proper_arc_isolated_contact_gap
    a.toContinuousMap hb (anchor '' Set.Icc r 1) hfin c (by change (0 : ℝ) < (c : ℝ) ∧ (c : ℝ) < 1; norm_num [c]) hcK
  obtain ⟨q,hcq,hqu⟩ := exists_between hcu
  refine ⟨q,hcq,hqu.trans_le u.property.2,?_,?_⟩
  · intro t ht hK
    by_cases htc : (t : ℝ) ≤ 1/2
    · have hp := regionalRawSurgeryBranch_first_half_mem_prefix anchor old r s hcontact right t htc
      obtain ⟨z,hz,he⟩ := hp
      obtain ⟨v,hv,hvE⟩ := hK
      have hzv : z = v := ha.injective (he.trans hvE.symm)
      have hzr : z = r := le_antisymm hz.2 (hzv ▸ hv.1)
      have hec : a t = a c := he.symm.trans ((congrArg anchor hzr).trans
        (hcontact.trans hc.symm))
      exact congrArg Subtype.val (hb.injective hec)
    · have hct : c < t := lt_of_not_ge htc
      exact congrArg Subtype.val ((hgap t ⟨hlc.trans hct,ht.2.trans_lt hqu⟩).mp hK)
  · intro t hqt
    refine ⟨regionalRawSurgeryBranch_second_half_mem_old anchor old r s hcontact right t
      (hcq.trans_le hqt),?_⟩
    intro he
    have htc : t = c := hb.injective ((Set.mem_singleton_iff.mp he).trans hc.symm)
    exact (not_le_of_gt hcq) (htc ▸ hqt)

#print axioms regional_raw_branch_tail_cutoff
