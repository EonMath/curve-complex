import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalFirstContactNegativeIncoming
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalNegativeBandTranslation
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalStripIncomingSide

open CurveComplex Set Topology

theorem regional_first_contact_strip_old_branch_common_face
    {S : Type} [TopologicalSpace S] [T2Space S]
    (F B : Set S) (hF : IsCompact F) (hBFront : B ⊆ frontier F)
    (anchor old : C(Interval,↥F)) (hold : Topology.IsEmbedding old)
    (l r s : Interval) (hlr : l < r)
    (hcontact : anchor r = old s)
    (hfirst : ∀ u : Interval, u < r → anchor u ∉ Set.range old)
    (E : C(Interval × Set.Icc (-1 : ℝ) 1,↥F))
    (hE : Topology.IsEmbedding E)
    (hcenter : ∀ t, E (t,⟨0,by norm_num⟩) = old t)
    (hend : ∀ w, (E (0,w)).val ∈ B ∧ (E (1,w)).val ∈ B)
    (hint : ∀ t ∈ Set.Ioo (0 : Interval) 1, ∀ w,
      (E (t,w)).val ∈ interior F)
    (hopen : IsOpen (E '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}))
    (hin : ∀ t ∈ Set.Ico l r, anchor t ∈ Set.range E)
    (right : Bool) :
    ∃ b : C(Interval,↥F),
      Topology.IsEmbedding b ∧
      (b 0).val ∈ B ∧ (b 1).val ∈ B ∧
      (∀ t ∈ Set.Ioo (0 : Interval) 1, (b t).val ∉ frontier F) ∧
      Disjoint (Set.range b) (Set.range old) ∧
      Disjoint (Set.range b)
        (Set.range (regionalRawSurgeryBranch anchor old r s hcontact right)) ∧
      ∃ H : AmbientIsotopy ↥F,
        (∀ t, (fun y => H.map (t,y)) '' {y : ↥F | y.val ∈ B} =
          {y : ↥F | y.val ∈ B}) ∧
        (∀ t, (fun y => H.map (t,y)) '' {y : ↥F | y.val ∈ frontier F} =
          {y : ↥F | y.val ∈ frontier F}) ∧
        H.finalMap '' Set.range old = Set.range b ∧
        (∀ t y, y ∉ Set.range E → H.map (t,y) = y) := by
  rcases regional_first_contact_incoming_strip_one_side
      anchor old E hE hcenter l r hlr hin hfirst with hneg | hpos
  · exact regional_first_contact_negative_incoming_common_face
      F B hF hBFront anchor old hold l r s hlr hcontact hfirst
      E hE hcenter hend hint hopen hin hneg right
  · let N := regionalReflectedStrip E
    have hN : Topology.IsEmbedding N := regionalReflectedStrip_embedding E hE
    have hNcenter : ∀ t, N (t,⟨0,by norm_num⟩) = old t := by
      intro t
      simpa [N,regionalReflectedStrip,regionalStripReflect] using hcenter t
    have hNend : ∀ w, (N (0,w)).val ∈ B ∧ (N (1,w)).val ∈ B :=
      fun w => hend (regionalStripReflect w)
    have hNint : ∀ t ∈ Set.Ioo (0 : Interval) 1, ∀ w,
        (N (t,w)).val ∈ interior F :=
      fun t ht w => hint t ht (regionalStripReflect w)
    have hNopen : IsOpen (N '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}) := by
      rw [show N '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1} =
        E '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1} from
        regionalReflectedStrip_core_image E]
      exact hopen
    have hinN : ∀ t ∈ Set.Ico l r, anchor t ∈ Set.range N := by
      intro t ht
      rw [show Set.range N = Set.range E from regionalReflectedStrip_range E]
      exact hin t ht
    have hnegN : ∀ t (ht : t ∈ Set.Ico l r),
        ((hN.toHomeomorph.symm ⟨anchor t,hinN t ht⟩).2 : ℝ) < 0 := by
      intro t ht
      let q := hE.toHomeomorph.symm ⟨anchor t,hin t ht⟩
      have hEq : E q = anchor t := congrArg Subtype.val
        (hE.toHomeomorph.apply_symm_apply ⟨anchor t,hin t ht⟩)
      have hNq : N (q.1,regionalStripReflect q.2) = anchor t := by
        change E (q.1,regionalStripReflect (regionalStripReflect q.2)) = anchor t
        rw [regionalStripReflect_involutive]
        exact hEq
      have hinv : hN.toHomeomorph.symm ⟨anchor t,hinN t ht⟩ =
          (q.1,regionalStripReflect q.2) := by
        calc
          hN.toHomeomorph.symm ⟨anchor t,hinN t ht⟩ =
              hN.toHomeomorph.symm
                ⟨N (q.1,regionalStripReflect q.2),Set.mem_range_self _⟩ :=
            congrArg hN.toHomeomorph.symm (Subtype.ext hNq.symm)
          _ = (q.1,regionalStripReflect q.2) :=
            hN.toHomeomorph.symm_apply_apply _
      rw [hinv]
      change -(q.2 : ℝ) < 0
      linarith [hpos t ht]
    obtain ⟨b,hb,hb0,hb1,hbp,hba,hbranch,H,hHB,hHF,hmove,hout⟩ :=
      regional_first_contact_negative_incoming_common_face
        F B hF hBFront anchor old hold l r s hlr hcontact hfirst
        N hN hNcenter hNend hNint hNopen hinN hnegN right
    refine ⟨b,hb,hb0,hb1,hbp,hba,hbranch,H,hHB,hHF,hmove,?_⟩
    intro t y hy
    apply hout t y
    rw [show Set.range N = Set.range E from regionalReflectedStrip_range E]
    exact hy

#print axioms regional_first_contact_strip_old_branch_common_face
