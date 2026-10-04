import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches

open CurveComplex Set Topology

theorem regional_outgoing_strip_one_side
    {S : Type} [TopologicalSpace S] [T2Space S] {F : Set S}
    (anchor old : C(Interval,↥F))
    (E : C(Interval × Set.Icc (-1 : ℝ) 1,↥F))
    (hE : Topology.IsEmbedding E)
    (hcenter : ∀ t, E (t,⟨0,by norm_num⟩) = anchor t)
    (s u : Interval) (hsu : s < u)
    (hin : ∀ t ∈ Set.Ioc s u, old t ∈ Set.range E)
    (havoid : ∀ t ∈ Set.Ioc s u, old t ∉ Set.range anchor) :
    (∀ t (ht : t ∈ Set.Ioc s u),
      ((hE.toHomeomorph.symm ⟨old t,hin t ht⟩).2 : ℝ) < 0) ∨
    (∀ t (ht : t ∈ Set.Ioc s u),
      0 < ((hE.toHomeomorph.symm ⟨old t,hin t ht⟩).2 : ℝ)) := by
  classical
  let z : Interval → ℝ := fun t =>
    if ht : old t ∈ Set.range E then
      ((hE.toHomeomorph.symm ⟨old t,ht⟩).2 : ℝ)
    else 0
  have hz_at (t : Interval) (ht : t ∈ Set.Ioc s u) :
      z t = ((hE.toHomeomorph.symm ⟨old t,hin t ht⟩).2 : ℝ) := by
    dsimp only [z]
    rw [dite_eq_left (hin t ht)]
  have hzc : ContinuousOn z (Set.Ioc s u) := by
    rw [continuousOn_iff_continuous_domRestrict]
    let f : Set.Ioc s u → Set.range E :=
      fun t => ⟨old t.val,hin t.val t.property⟩
    have hf : Continuous f :=
      (old.continuous.comp continuous_subtype_val).subtype_mk _
    have hz' : Continuous (fun t : Set.Ioc s u =>
        ((hE.toHomeomorph.symm (f t)).2 : ℝ)) := by
      fun_prop
    convert hz' using 1
    funext t
    exact hz_at t.val t.property
  have hnonzero : ∀ t ∈ Set.Ioc s u, z t ≠ 0 := by
    intro t ht hz
    let q := hE.toHomeomorph.symm ⟨old t,hin t ht⟩
    have hq0 : q.2 = ⟨0,by norm_num⟩ := Subtype.ext (by
      change ((hE.toHomeomorph.symm ⟨old t,hin t ht⟩).2 : ℝ) = 0
      rw [← hz_at t ht]
      exact hz)
    have he : E q = old t :=
      congrArg Subtype.val
        (hE.toHomeomorph.apply_symm_apply ⟨old t,hin t ht⟩)
    apply havoid t ht
    rw [← he, show q = (q.1,⟨0,by norm_num⟩) from Prod.ext rfl hq0]
    exact ⟨q.1,(hcenter q.1).symm⟩
  have hu : u ∈ Set.Ioc s u := ⟨hsu,le_refl _⟩
  rcases lt_or_gt_of_ne (hnonzero u hu) with hneg | hpos
  · left
    intro t ht
    have hzneg := isPreconnected_Ioc.gt_of_ne hzc hnonzero
      ⟨u,hu,hneg⟩ ht
    rw [hz_at t ht] at hzneg
    exact hzneg
  · right
    intro t ht
    have hzpos := isPreconnected_Ioc.lt_of_ne hzc hnonzero
      ⟨u,hu,hpos⟩ ht
    rw [hz_at t ht] at hzpos
    exact hzpos

#print axioms regional_outgoing_strip_one_side
