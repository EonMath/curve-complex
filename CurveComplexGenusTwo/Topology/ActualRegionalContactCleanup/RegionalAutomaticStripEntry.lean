import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalFirstContactTwoSidedCommonFace

open CurveComplex Set Topology

theorem regional_first_contact_enters_open_strip
    {S : Type} [TopologicalSpace S] [T2Space S] {F : Set S}
    (anchor old : C(Interval,↥F))
    (r s : Interval) (hr : (0 : Interval) < r)
    (hcontact : anchor r = old s)
    (E : C(Interval × Set.Icc (-1 : ℝ) 1,↥F))
    (hcenter : ∀ t, E (t,⟨0,by norm_num⟩) = old t)
    (hopen : IsOpen (E '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1})) :
    ∃ l : Interval, l < r ∧
      ∀ t ∈ Set.Ico l r, anchor t ∈ Set.range E := by
  let U : Set ↥F := E '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}
  have hrU : anchor r ∈ U := by
    refine ⟨(s,⟨0,by norm_num⟩),?_,?_⟩
    · norm_num
    · exact (hcontact.trans (hcenter s).symm).symm
  have hrOpen : IsOpen (anchor ⁻¹' U) := hopen.preimage anchor.continuous
  have hnhds : anchor ⁻¹' U ∈ 𝓝 r := hrOpen.mem_nhds hrU
  obtain ⟨l,hlr,hsub⟩ := exists_Ioc_subset_of_mem_nhds hnhds ⟨0,hr⟩
  obtain ⟨l',hll',hl'r⟩ := exists_between hlr
  refine ⟨l',hl'r,?_⟩
  intro t ht
  have htU : anchor t ∈ U := hsub ⟨lt_of_lt_of_le hll' ht.1,ht.2.le⟩
  obtain ⟨z,hz,he⟩ := htU
  exact ⟨z,he⟩

theorem regional_first_contact_strip_common_face_automatic
    {S : Type} [TopologicalSpace S] [T2Space S]
    (F B : Set S) (hF : IsCompact F) (hBFront : B ⊆ frontier F)
    (anchor old : C(Interval,↥F)) (hold : Topology.IsEmbedding old)
    (r s : Interval) (hr : (0 : Interval) < r)
    (hcontact : anchor r = old s)
    (hfirst : ∀ u : Interval, u < r → anchor u ∉ Set.range old)
    (E : C(Interval × Set.Icc (-1 : ℝ) 1,↥F))
    (hE : Topology.IsEmbedding E)
    (hcenter : ∀ t, E (t,⟨0,by norm_num⟩) = old t)
    (hend : ∀ w, (E (0,w)).val ∈ B ∧ (E (1,w)).val ∈ B)
    (hint : ∀ t ∈ Set.Ioo (0 : Interval) 1, ∀ w,
      (E (t,w)).val ∈ interior F)
    (hopen : IsOpen (E '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}))
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
  obtain ⟨l,hlr,hin⟩ := regional_first_contact_enters_open_strip
    anchor old r s hr hcontact E hcenter hopen
  exact regional_first_contact_strip_old_branch_common_face
    F B hF hBFront anchor old hold l r s hlr hcontact hfirst
    E hE hcenter hend hint hopen hin right

#print axioms regional_first_contact_enters_open_strip
#print axioms regional_first_contact_strip_common_face_automatic
