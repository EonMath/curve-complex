import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalSmallWidthPrefixAvoidance

open CurveComplex Set Topology

theorem regional_first_contact_old_branch_common_face
    {S : Type} [TopologicalSpace S] [T2Space S]
    (F B : Set S) (hF : IsCompact F) (hBFront : B ⊆ frontier F)
    (anchor old : C(Interval,↥F)) (hold : Topology.IsEmbedding old)
    (r s : Interval) (hcontact : anchor r = old s)
    (hfirst : ∀ u : Interval, u < r → anchor u ∉ Set.range old)
    (E : C(Interval × Set.Icc (-1 : ℝ) 1,↥F))
    (hE : Topology.IsEmbedding E)
    (hcenter : ∀ t, E (t,⟨0,by norm_num⟩) = old t)
    (hend : ∀ w, (E (0,w)).val ∈ B ∧ (E (1,w)).val ∈ B)
    (hint : ∀ t ∈ Set.Ioo (0 : Interval) 1, ∀ w,
      (E (t,w)).val ∈ interior F)
    (hopen : IsOpen (E '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}))
    (V : Set Interval) (hV : IsOpen V) (hsV : s ∈ V)
    (η : ℝ) (hη : 0 < η)
    (hnear : ∀ t ∈ V, ∀ w : Set.Icc (-1 : ℝ) 1,
      0 < (w : ℝ) → (w : ℝ) < η →
      E (t,w) ∉ anchor '' Set.Icc 0 r)
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
  let K : Set ↥F := anchor '' Set.Icc 0 r
  have hK : IsClosed K :=
    ((isCompact_Icc.image anchor.continuous).isClosed)
  have hinter := regional_first_contact_prefix_inter anchor old r s hcontact hfirst
  have hfar : ∀ t ∈ Vᶜ, old t ∉ K := by
    intro t ht hKmem
    have htInter : old t ∈ K ∩ Set.range old :=
      ⟨hKmem,Set.mem_range_self t⟩
    rw [hinter] at htInter
    have hts : t = s := hold.injective (Set.mem_singleton_iff.mp htInter)
    exact ht (hts ▸ hsV)
  obtain ⟨ε,hε0,hε1,b,hb,hb0,hb1,hbp,hbOld,hbK,H,hHB,hHF,hmove,hout⟩ :=
    regional_strip_local_side_gives_global_ambient_copy F B hF hBFront
      old E hE hcenter hend hint hopen K hK V hV hfar η hη hnear
  have hbBranch : Disjoint (Set.range b)
      (Set.range (regionalRawSurgeryBranch anchor old r s hcontact right)) := by
    rw [regionalRawSurgeryBranch_range]
    apply Set.disjoint_union_right.mpr
    constructor
    · exact hbK
    · apply Set.disjoint_left.mpr
      rintro y hy ⟨t,ht,rfl⟩
      exact Set.disjoint_left.mp hbOld hy (Set.mem_range_self t)
  exact ⟨b,hb,hb0,hb1,hbp,hbOld,hbBranch,H,hHB,hHF,hmove,hout⟩

#print axioms regional_first_contact_old_branch_common_face
