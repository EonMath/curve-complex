import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalOutgoingTailSideClearance
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalProperProfileAmbientMove
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalRawBranchParameterSplit
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalRawBranchTailCutoff
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalTaperedProfileClearance

open CurveComplex Set Topology

theorem regional_raw_branch_negative_profile_cleanup
    {S : Type} [TopologicalSpace S] [T2Space S] {F : Set S}
    (B : Set S) (hBF : B ⊆ frontier F) (hF : IsCompact F)
    (anchor old : C(Interval,↥F)) (ha : Topology.IsEmbedding anchor)
    (r s : Interval) (hcontact : anchor r = old s) (right : Bool)
    (hb : Topology.IsEmbedding (regionalRawSurgeryBranch anchor old r s hcontact right))
    (hfinite : (Set.range old ∩ Set.range anchor).Finite)
    (E : C(Interval × Set.Icc (-1 : ℝ) 1,↥F))
    (hE : Topology.IsEmbedding E)
    (hcenter : ∀ t, E (t,⟨0,by norm_num⟩) =
      regionalRawSurgeryBranch anchor old r s hcontact right t)
    (hend : ∀ w, (E (0,w)).val ∈ B ∧ (E (1,w)).val ∈ B)
    (hint : ∀ t ∈ Set.Ioo (0 : Interval) 1, ∀ w, (E (t,w)).val ∈ interior F)
    (hopen : IsOpen (E '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}))
    (u : Interval) (hru : r < u)
    (hin : ∀ z ∈ Set.Ioc r u, anchor z ∈ Set.range E)
    (hneg : ∀ z (hz : z ∈ Set.Ioc r u),
      ((hE.toHomeomorph.symm ⟨anchor z,hin z hz⟩).2 : ℝ) < 0) :
    ∃ b : C(Interval,↥F), Topology.IsEmbedding b ∧
      (b 0).val ∈ B ∧ (b 1).val ∈ B ∧
      (∀ t ∈ Set.Ioo (0 : Interval) 1, (b t).val ∉ frontier F) ∧
      Set.range b ⊆ Set.range E ∧
      Set.range b ∩ Set.range anchor ⊆
        (Set.range old ∩ Set.range anchor) \ {old s} ∧
      ∃ H : AmbientIsotopy ↥F,
        (∀ t, (fun y => H.map (t,y)) '' {y : ↥F | y.val ∈ B} =
          {y : ↥F | y.val ∈ B}) ∧
        (∀ t, (fun y => H.map (t,y)) '' {y : ↥F | y.val ∈ frontier F} =
          {y : ↥F | y.val ∈ frontier F}) ∧
        H.finalMap '' Set.range (regionalRawSurgeryBranch anchor old r s hcontact right) =
          Set.range b ∧
        (∀ t y, y ∉ Set.range E → H.map (t,y) = y) := by
  let a := regionalRawSurgeryBranch anchor old r s hcontact right
  let c : Interval := ⟨1/2,by norm_num⟩
  let K : Set ↥F := anchor '' Set.Icc r 1
  have hK : IsClosed K := (isCompact_Icc.image anchor.continuous).isClosed
  have hc : anchor r = a c := hcontact.trans
    (regionalRawSurgeryBranch_half_contact anchor old r s hcontact right).symm
  obtain ⟨q,hcq,hq1,hsole,hafter⟩ := regional_raw_branch_tail_cutoff
    anchor old ha r s hcontact right hb hfinite
  obtain ⟨V,hV,hcV,η,hη,hnear⟩ := regional_outgoing_negative_tail_near_center_clearance
    a.toContinuousMap anchor ha E hE hcenter r c u hru hc hin hneg
  obtain ⟨ε,hε,hpos,hzero,hεK⟩ := regional_tapered_profile_avoids_prefix_obstacle
    E K hK c q V hV hcV (by
      intro t ht hmem
      apply Subtype.ext
      exact hsole t ht (hcenter t ▸ hmem)) η hη hnear
  let b : C(Interval,↥F) :=
    ⟨fun t => E (t,⟨ε t,⟨by linarith [(hε t).1],(hε t).2.le⟩⟩),by fun_prop⟩
  have hbEmb : Topology.IsEmbedding b :=
    (b.continuous.isClosedEmbedding (by
      intro t z he
      exact congrArg Prod.fst (hE.injective he))).isEmbedding
  have hbRange : Set.range b ⊆ Set.range E := by
    rintro y ⟨t,rfl⟩
    exact Set.mem_range_self _
  have hprefix : anchor '' Set.Icc 0 r ⊆ Set.range a := by
    rw [regionalRawSurgeryBranch_range]
    exact Set.subset_union_left
  have hcontain : Set.range b ∩ Set.range anchor ⊆
      (Set.range old ∩ Set.range anchor) \ {old s} := by
    rintro y ⟨⟨t,rfl⟩,hy⟩
    by_cases ht : t < q
    · obtain ⟨z,hz⟩ := hy
      by_cases hrz : r ≤ z
      · exact False.elim (hεK t ht ⟨z,⟨hrz,z.property.2⟩,hz⟩)
      · have hraw : b t ∈ Set.range a := hprefix ⟨z,⟨z.property.1,(lt_of_not_ge hrz).le⟩,hz⟩
        obtain ⟨v,hv⟩ := hraw
        have he : E (t,⟨ε t,⟨by linarith [(hε t).1],(hε t).2.le⟩⟩) =
            E (v,⟨0,by norm_num⟩) := hv.symm.trans (hcenter v).symm
        have he0 := congrArg (fun z : Interval × Set.Icc (-1 : ℝ) 1 =>
          (z.2 : ℝ)) (hE.injective he)
        exact False.elim ((ne_of_gt (hpos t ht)) he0)
    · have hqt : q ≤ t := le_of_not_gt ht
      have he : b t = a t := by
        change E (t,_) = a t
        have hw0 : (⟨ε t,⟨by linarith [(hε t).1],(hε t).2.le⟩⟩ :
            Set.Icc (-1 : ℝ) 1) = ⟨0,by norm_num⟩ := Subtype.ext (hzero t hqt)
        rw [hw0,hcenter]
      have htail := hafter t hqt
      exact ⟨⟨he.symm ▸ htail.1,hy⟩,he.symm ▸ htail.2⟩
  obtain ⟨H,hHB,hHF,hmove,hout⟩ := regional_proper_strip_profile_ambient_move
    F B hF hBF E hE hend hint hopen ε (fun t => (hε t).1) (fun t => (hε t).2)
  refine ⟨b,hbEmb,(hend _).1,(hend _).2,?_,hbRange,hcontain,H,hHB,hHF,?_,hout⟩
  · intro t ht
    exact (mem_interior_iff_notMem_frontier (b t).property).mp (hint t ht _)
  · have hcenterRange : Set.range (fun t : Interval => E (t,⟨0,by norm_num⟩)) =
        Set.range a := by
      congr 1
      funext t
      exact hcenter t
    rw [hcenterRange] at hmove
    exact hmove

#print axioms regional_raw_branch_negative_profile_cleanup
