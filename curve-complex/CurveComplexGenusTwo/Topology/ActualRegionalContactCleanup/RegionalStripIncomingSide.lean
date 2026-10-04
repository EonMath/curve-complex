import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches

open CurveComplex Set Topology

theorem regional_first_contact_incoming_strip_one_side
    {S : Type} [TopologicalSpace S] [T2Space S] {F : Set S}
    (anchor old : C(Interval,↥F))
    (E : C(Interval × Set.Icc (-1 : ℝ) 1,↥F))
    (hE : Topology.IsEmbedding E)
    (hcenter : ∀ t, E (t,⟨0,by norm_num⟩) = old t)
    (l r : Interval) (hlr : l < r)
    (hin : ∀ t ∈ Set.Ico l r, anchor t ∈ Set.range E)
    (hfirst : ∀ t < r, anchor t ∉ Set.range old) :
    (∀ t (ht : t ∈ Set.Ico l r),
      ((hE.toHomeomorph.symm ⟨anchor t,hin t ht⟩).2 : ℝ) < 0) ∨
    (∀ t (ht : t ∈ Set.Ico l r),
      0 < ((hE.toHomeomorph.symm ⟨anchor t,hin t ht⟩).2 : ℝ)) := by
  classical
  let z : Interval → ℝ := fun t =>
    if ht : anchor t ∈ Set.range E then
      ((hE.toHomeomorph.symm ⟨anchor t,ht⟩).2 : ℝ)
    else 0
  have hz_at (t : Interval) (ht : t ∈ Set.Ico l r) :
      z t = ((hE.toHomeomorph.symm ⟨anchor t,hin t ht⟩).2 : ℝ) := by
    dsimp only [z]
    rw [dite_eq_left (hin t ht)]
  have hzc : ContinuousOn z (Set.Ico l r) := by
    rw [continuousOn_iff_continuous_domRestrict]
    let f : Set.Ico l r → Set.range E :=
      fun t => ⟨anchor t.val,hin t.val t.property⟩
    have hf : Continuous f :=
      (anchor.continuous.comp continuous_subtype_val).subtype_mk _
    have hz' : Continuous (fun t : Set.Ico l r =>
        ((hE.toHomeomorph.symm (f t)).2 : ℝ)) := by
      fun_prop
    convert hz' using 1
    funext t
    exact hz_at t.val t.property
  have havoid : ∀ t ∈ Set.Ico l r, z t ≠ 0 := by
    intro t ht hz
    have hrange := hin t ht
    have hcoord : ((hE.toHomeomorph.symm ⟨anchor t,hrange⟩).2 : ℝ) = 0 := by
      rw [← hz_at t ht]
      exact hz
    let q := hE.toHomeomorph.symm ⟨anchor t,hrange⟩
    have hq0 : q.2 = ⟨0,by norm_num⟩ := Subtype.ext hcoord
    have he : E q = anchor t := by
      exact congrArg Subtype.val
        (hE.toHomeomorph.apply_symm_apply ⟨anchor t,hrange⟩)
    have ha : anchor t ∈ Set.range old := by
      rw [← he, show q = (q.1,⟨0,by norm_num⟩) from Prod.ext rfl hq0]
      exact ⟨q.1,(hcenter q.1).symm⟩
    exact hfirst t ht.2 ha
  have hl : l ∈ Set.Ico l r := ⟨le_refl _,hlr⟩
  rcases lt_or_gt_of_ne (havoid l hl) with hneg | hpos
  · left
    intro t ht
    have hzneg := isPreconnected_Ico.gt_of_ne hzc havoid
      ⟨l,hl,hneg⟩ ht
    rw [hz_at t ht] at hzneg
    exact hzneg
  · right
    intro t ht
    have hzpos := isPreconnected_Ico.lt_of_ne hzc havoid
      ⟨l,hl,hpos⟩ ht
    rw [hz_at t ht] at hzpos
    exact hzpos

#print axioms regional_first_contact_incoming_strip_one_side
