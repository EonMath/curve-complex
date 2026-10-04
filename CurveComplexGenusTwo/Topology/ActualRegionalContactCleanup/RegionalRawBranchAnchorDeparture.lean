import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalOutgoingStripSide
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalRawBranchParameterSplit

open CurveComplex Set Topology

theorem regional_raw_branch_anchor_departure_window
    {S : Type} [TopologicalSpace S] [T2Space S] {F : Set S}
    (anchor old : C(Interval,↥F)) (ha : Topology.IsEmbedding anchor)
    (r s : Interval) (hr : r ∈ Set.Ioo (0 : Interval) 1)
    (hcontact : anchor r = old s) (right : Bool)
    (hfinite : (Set.range old ∩ Set.range anchor).Finite)
    (E : C(Interval × Set.Icc (-1 : ℝ) 1,↥F))
    (hE : Topology.IsEmbedding E)
    (hcenter : ∀ t, E (t,⟨0,by norm_num⟩) =
      regionalRawSurgeryBranch anchor old r s hcontact right t)
    (hopen : IsOpen (E '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1})) :
    ∃ u : Interval, ∃ _hru : r < u,
      ∃ hin : ∀ z ∈ Set.Ioc r u, anchor z ∈ Set.range E,
        (∀ z ∈ Set.Ioc r u, anchor z ∉
          Set.range (regionalRawSurgeryBranch anchor old r s hcontact right)) ∧
        ((∀ z (hz : z ∈ Set.Ioc r u),
          ((hE.toHomeomorph.symm ⟨anchor z,hin z hz⟩).2 : ℝ) < 0) ∨
         (∀ z (hz : z ∈ Set.Ioc r u),
          0 < ((hE.toHomeomorph.symm ⟨anchor z,hin z hz⟩).2 : ℝ))) := by
  let a := regionalRawSurgeryBranch anchor old r s hcontact right
  obtain ⟨l,v,hlr,hrv,hgap⟩ := regional_proper_arc_isolated_contact_gap
    anchor ha (Set.range old) (by rwa [Set.inter_comm]) r hr ⟨s,hcontact.symm⟩
  let U : Set ↥F := E '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}
  have hrU : anchor r ∈ U := by
    refine ⟨(⟨1/2,by norm_num⟩,⟨0,by norm_num⟩),by norm_num,?_⟩
    exact (hcenter _).trans
      ((regionalRawSurgeryBranch_half_contact anchor old r s hcontact right).trans hcontact.symm)
  obtain ⟨w,hrw,hw⟩ := exists_Ico_subset_of_mem_nhds
    ((hopen.preimage anchor.continuous).mem_nhds hrU) ⟨1,hr.2⟩
  obtain ⟨u,hru,hu⟩ := exists_between (lt_min hrv hrw)
  have huv : u < v := hu.trans_le (min_le_left v w)
  have huw : u < w := hu.trans_le (min_le_right v w)
  have hin : ∀ z ∈ Set.Ioc r u, anchor z ∈ Set.range E := by
    intro z hz
    exact Set.image_subset_range _ _ (hw ⟨hz.1.le,hz.2.trans_lt huw⟩)
  have havoid : ∀ z ∈ Set.Ioc r u, anchor z ∉ Set.range a := by
    intro z hz hbad
    rw [regionalRawSurgeryBranch_range] at hbad
    rcases hbad with ⟨t,ht,he⟩ | ⟨t,ht,he⟩
    · have htz : t = z := ha.injective he
      exact (not_le_of_gt hz.1) (htz ▸ ht.2)
    · have hzold : anchor z ∈ Set.range old := ⟨t,he⟩
      exact hz.1.ne' ((hgap z ⟨hlr.trans hz.1,hz.2.trans_lt huv⟩).mp hzold)
  refine ⟨u,hru,hin,havoid,?_⟩
  exact regional_outgoing_strip_one_side a.toContinuousMap anchor E hE hcenter
    r u hru hin havoid

#print axioms regional_raw_branch_anchor_departure_window
