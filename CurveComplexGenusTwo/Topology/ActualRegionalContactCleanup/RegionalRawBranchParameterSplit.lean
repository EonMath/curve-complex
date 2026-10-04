import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches

open CurveComplex Set Topology

theorem regionalRawSurgeryBranch_half_contact
    {S : Type} [TopologicalSpace S] {F : Set S}
    (anchor old : C(Interval,↥F)) (r s : Interval)
    (hcontact : anchor r = old s) (right : Bool) :
    regionalRawSurgeryBranch anchor old r s hcontact right
      ⟨1/2,by norm_num⟩ = old s := by
  cases right <;>
    simp [regionalRawSurgeryBranch,Path.trans_apply,Path.cast_coe,
      Path.subpath,Path.target]

theorem regionalRawSurgeryBranch_second_half_mem_old
    {S : Type} [TopologicalSpace S] {F : Set S}
    (anchor old : C(Interval,↥F)) (r s : Interval)
    (hcontact : anchor r = old s) (right : Bool)
    (t : Interval) (ht : (1/2 : ℝ) < t) :
    regionalRawSurgeryBranch anchor old r s hcontact right t ∈ Set.range old := by
  cases right <;>
    simp only [regionalRawSurgeryBranch,Path.trans_apply,
      show ¬ (t : ℝ) ≤ 1/2 from not_le.mpr ht,dite_eq_right,Path.cast_coe]
  all_goals
    apply Set.image_subset_range old Set.univ
    exact ⟨_,Set.mem_univ _,rfl⟩

#print axioms regionalRawSurgeryBranch_half_contact
#print axioms regionalRawSurgeryBranch_second_half_mem_old

theorem regionalRawSurgeryBranch_first_half_mem_prefix
    {S : Type} [TopologicalSpace S] {F : Set S}
    (anchor old : C(Interval,↥F)) (r s : Interval)
    (hcontact : anchor r = old s) (right : Bool)
    (t : Interval) (ht : (t : ℝ) ≤ 1/2) :
    regionalRawSurgeryBranch anchor old r s hcontact right t ∈
      anchor '' Set.Icc 0 r := by
  let β : Path (anchor 0) (anchor 1) :=
    { toContinuousMap := anchor,source' := rfl,target' := rfl }
  have hm : (β.subpath 0 r) ⟨2*(t : ℝ),by constructor <;> linarith [t.property.1]⟩ ∈
      Set.range (β.subpath 0 r) := Set.mem_range_self _
  rw [Path.range_subpath_of_le _ _ _ r.property.1] at hm
  change (β.subpath 0 r) ⟨2*(t : ℝ),by constructor <;> linarith [t.property.1]⟩ ∈
    anchor '' Set.Icc 0 r at hm
  cases right <;>
    simpa only [β,regionalRawSurgeryBranch,Path.trans_apply,ht,dite_eq_left,
      Path.cast_coe] using hm

/-- The raw branch meets the remaining anchor tail only finitely, even though
    its intersection with the whole anchor contains a shared prefix. -/
theorem regionalRawSurgeryBranch_remaining_anchor_contacts_finite
    {S : Type} [TopologicalSpace S] {F : Set S}
    (anchor old : C(Interval,↥F)) (ha : Topology.IsEmbedding anchor)
    (r s : Interval) (hcontact : anchor r = old s) (right : Bool)
    (hfinite : (Set.range old ∩ Set.range anchor).Finite) :
    (Set.range (regionalRawSurgeryBranch anchor old r s hcontact right) ∩
      (anchor '' Set.Icc r 1)).Finite := by
  have hp : ((anchor '' Set.Icc 0 r) ∩ (anchor '' Set.Icc r 1)).Finite := by
    apply Set.Finite.subset (Set.finite_singleton (anchor r))
    rintro y ⟨⟨t,ht,he⟩,⟨u,hu,he'⟩⟩
    have htu : t = u := ha.injective (he.trans he'.symm)
    have htr : t = r := le_antisymm ht.2 (htu ▸ hu.1)
    exact Set.mem_singleton_iff.mpr (he.symm.trans (congrArg anchor htr))
  have ho : ((old '' (if right then Set.Icc s 1 else Set.Icc 0 s)) ∩
      (anchor '' Set.Icc r 1)).Finite :=
    hfinite.subset (Set.inter_subset_inter (Set.image_subset_range _ _)
      (Set.image_subset_range _ _))
  rw [regionalRawSurgeryBranch_range,Set.union_inter_distrib_right]
  exact hp.union ho

#print axioms regionalRawSurgeryBranch_first_half_mem_prefix
#print axioms regionalRawSurgeryBranch_remaining_anchor_contacts_finite
