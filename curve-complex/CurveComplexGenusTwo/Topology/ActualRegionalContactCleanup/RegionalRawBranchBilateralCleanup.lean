import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalNegativeBandTranslation
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalRawBranchAnchorDeparture
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalRawBranchProfileCleanup

open CurveComplex Set Topology

theorem regional_raw_branch_profile_cleanup
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
    (hr : r ∈ Set.Ioo (0 : Interval) 1) :
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
  obtain ⟨u,hru,hin,havoid,hside⟩ := regional_raw_branch_anchor_departure_window
    anchor old ha r s hr hcontact right hfinite E hE hcenter hopen
  rcases hside with hn | hp
  · exact regional_raw_branch_negative_profile_cleanup B hBF hF anchor old ha
      r s hcontact right hb hfinite E hE hcenter hend hint hopen u hru hin hn
  · let N := regionalReflectedStrip E
    have hN := regionalReflectedStrip_embedding E hE
    have hNc : ∀ t, N (t,⟨0,by norm_num⟩) =
        regionalRawSurgeryBranch anchor old r s hcontact right t := by
      intro t
      simpa [N,regionalReflectedStrip,regionalStripReflect] using hcenter t
    have hNe : ∀ w, (N (0,w)).val ∈ B ∧ (N (1,w)).val ∈ B :=
      fun w => hend (regionalStripReflect w)
    have hNi : ∀ t ∈ Set.Ioo (0 : Interval) 1, ∀ w,
        (N (t,w)).val ∈ interior F := fun t ht w => hint t ht (regionalStripReflect w)
    have hNo : IsOpen (N '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}) := by
      rw [show N '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1} =
        E '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1} from
        regionalReflectedStrip_core_image E]
      exact hopen
    have hRange : Set.range N = Set.range E := regionalReflectedStrip_range E
    have hinN : ∀ z ∈ Set.Ioc r u, anchor z ∈ Set.range N := by
      intro z hz
      rw [hRange]
      exact hin z hz
    have hnN : ∀ z (hz : z ∈ Set.Ioc r u),
        ((hN.toHomeomorph.symm ⟨anchor z,hinN z hz⟩).2 : ℝ) < 0 := by
      intro z hz
      let q := hE.toHomeomorph.symm ⟨anchor z,hin z hz⟩
      have hEq : E q = anchor z := congrArg Subtype.val
        (hE.toHomeomorph.apply_symm_apply ⟨anchor z,hin z hz⟩)
      have hNq : N (q.1,regionalStripReflect q.2) = anchor z := by
        change E (q.1,regionalStripReflect (regionalStripReflect q.2)) = anchor z
        rw [regionalStripReflect_involutive]
        exact hEq
      have hinv : hN.toHomeomorph.symm ⟨anchor z,hinN z hz⟩ =
          (q.1,regionalStripReflect q.2) := by
        calc
          hN.toHomeomorph.symm ⟨anchor z,hinN z hz⟩ =
              hN.toHomeomorph.symm ⟨N (q.1,regionalStripReflect q.2),Set.mem_range_self _⟩ :=
            congrArg hN.toHomeomorph.symm (Subtype.ext hNq.symm)
          _ = (q.1,regionalStripReflect q.2) := hN.toHomeomorph.symm_apply_apply _
      rw [hinv]
      change -(q.2 : ℝ) < 0
      linarith [hp z hz]
    obtain ⟨b,hbE,hb0,hb1,hbp,hbRange,hcontacts,H,hHB,hHF,hmove,hout⟩ :=
      regional_raw_branch_negative_profile_cleanup B hBF hF anchor old ha
        r s hcontact right hb hfinite N hN hNc hNe hNi hNo u hru hinN hnN
    exact ⟨b,hbE,hb0,hb1,hbp,hRange ▸ hbRange,hcontacts,H,hHB,hHF,hmove,
      (fun t y hy => hout t y (hRange.symm ▸ hy))⟩

#print axioms regional_raw_branch_profile_cleanup
