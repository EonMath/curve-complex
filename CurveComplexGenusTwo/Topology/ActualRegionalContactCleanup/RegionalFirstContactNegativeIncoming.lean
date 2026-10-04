import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalFirstContactCommonFace
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalStripPointClearance

open CurveComplex Set Topology

theorem regional_first_contact_negative_incoming_common_face
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
    (hneg : ∀ t (ht : t ∈ Set.Ico l r),
      ((hE.toHomeomorph.symm ⟨anchor t,hin t ht⟩).2 : ℝ) < 0)
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
  let K₀ : Set ↥F := anchor '' Set.Icc 0 l
  have hK₀ : IsClosed K₀ :=
    (isCompact_Icc.image anchor.continuous).isClosed
  have hsClear : E (s,⟨0,by norm_num⟩) ∉ K₀ := by
    rintro ⟨u,hu,he⟩
    exact hfirst u (lt_of_le_of_lt hu.2 hlr)
      ⟨s,(he.trans (hcenter s)).symm⟩
  obtain ⟨V,hV,hsV,η,hη,hK₀clear⟩ :=
    regional_strip_point_closed_obstacle_clearance E K₀ hK₀ s hsClear
  have hnear : ∀ t ∈ V, ∀ w : Set.Icc (-1 : ℝ) 1,
      0 < (w : ℝ) → (w : ℝ) < η →
      E (t,w) ∉ anchor '' Set.Icc 0 r := by
    intro t ht w hw hηw
    rintro ⟨u,hu,he⟩
    by_cases hul : u ≤ l
    · exact hK₀clear t ht w (by rw [abs_of_pos hw]; exact hηw)
        ⟨u,⟨hu.1,hul⟩,he⟩
    · have hlu : l < u := lt_of_not_ge hul
      rcases lt_or_eq_of_le hu.2 with hur | hur
      · have huI : u ∈ Set.Ico l r := ⟨hlu.le,hur⟩
        have hinv : hE.toHomeomorph.symm ⟨anchor u,hin u huI⟩ = (t,w) := by
          calc
            hE.toHomeomorph.symm ⟨anchor u,hin u huI⟩ =
                hE.toHomeomorph.symm ⟨E (t,w),Set.mem_range_self (t,w)⟩ :=
              congrArg hE.toHomeomorph.symm (Subtype.ext he)
            _ = (t,w) := hE.toHomeomorph.symm_apply_apply (t,w)
        have hsgn := hneg u huI
        rw [hinv] at hsgn
        exact (lt_asymm hsgn hw).elim
      · have he0 : E (t,w) = E (s,⟨0,by norm_num⟩) := by
          calc
            E (t,w) = anchor u := he.symm
            _ = anchor r := congrArg anchor hur
            _ = old s := hcontact
            _ = E (s,⟨0,by norm_num⟩) := (hcenter s).symm
        have hw0 := congrArg (fun z : Interval × Set.Icc (-1 : ℝ) 1 =>
          (z.2 : ℝ)) (hE.injective he0)
        exact (ne_of_gt hw) hw0
  exact regional_first_contact_old_branch_common_face F B hF hBFront
    anchor old hold r s hcontact hfirst E hE hcenter hend hint hopen
    V hV hsV η hη hnear right

#print axioms regional_first_contact_negative_incoming_common_face
