import CurveComplexGenusTwo.Dictionary.MarkedSphere
import Mathlib

open Set Topology Filter

private abbrev OpenInterval := Set.Ioo (0 : CurveComplex.Interval) 1

theorem proper_strip_uniform_ends_at_puncture'
    {X W : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace W] (p : X)
    (F : ℝ × W → {x : X // x ≠ p}) (hF : IsProperMap F)
    (V : Set X) (hV : IsOpen V) (hp : p ∈ V) :
    ∃ R : ℝ, ∀ t : ℝ, ∀ w : W, R ≤ |t| → (F (t, w)).val ∈ V := by
  let K : Set {x : X // x ≠ p} := (Subtype.val : {x : X // x ≠ p} → X) ⁻¹' Vᶜ
  have hVK : IsCompact (Vᶜ : Set X) := hV.isClosed_compl.isCompact
  have himage : (Subtype.val : {x : X // x ≠ p} → X) '' K = Vᶜ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      have hxp : x ≠ p := by
        intro he
        exact hx (he ▸ hp)
      exact ⟨⟨x, hxp⟩, hx, rfl⟩
  have hK : IsCompact K := Subtype.isCompact_iff.mpr (himage ▸ hVK)
  have hpre : IsCompact (F ⁻¹' K) := hF.isCompact_preimage hK
  have habs : IsCompact ((fun z : ℝ × W => |z.1|) '' (F ⁻¹' K)) :=
    hpre.image (continuous_abs.comp continuous_fst)
  obtain ⟨R, hR⟩ := habs.bddAbove
  refine ⟨R + 1, ?_⟩
  intro t w ht
  by_contra hnot
  have hmem : |t| ∈ (fun z : ℝ × W => |z.1|) '' (F ⁻¹' K) :=
    ⟨(t, w), hnot, rfl⟩
  have hbound := hR hmem
  linarith

noncomputable def properStripCompactification
    {X W : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace W] (p : X)
    (F : C(ℝ × W, {x : X // x ≠ p})) (hF : IsProperMap F)
    (r : ℝ ≃ₜ OpenInterval) : C(CurveComplex.Interval × W, X) := by
  let G : CurveComplex.Interval × W → X := fun z =>
    if hs : z.1 ∈ OpenInterval then
      (F (r.symm ⟨z.1, hs⟩, z.2)).val
    else p
  have hG : Continuous G := by
    let O : Set (CurveComplex.Interval × W) := {z | z.1 ∈ OpenInterval}
    have hO : IsOpen O := isOpen_Ioo.preimage continuous_fst
    have hOn : ContinuousOn G O := by
      rw [continuousOn_iff_continuous_domRestrict]
      have hs : Continuous (fun z : O => (⟨z.val.1, z.property⟩ : OpenInterval)) :=
        (continuous_fst.comp continuous_subtype_val).subtype_mk _
      have hw : Continuous (fun z : O => z.val.2) :=
        continuous_snd.comp continuous_subtype_val
      have hc : Continuous (fun z : O =>
          (F (r.symm ⟨z.val.1, z.property⟩, z.val.2)).val) :=
        continuous_subtype_val.comp
          (F.continuous.comp ((r.symm.continuous.comp hs).prodMk hw))
      apply hc.congr
      intro z
      change (F (r.symm ⟨z.val.1, z.property⟩, z.val.2)).val = G z
      have hz' : z.val.1 ∈ OpenInterval := z.property
      change (0 : CurveComplex.Interval) < z.val.1 ∧ z.val.1 < 1 at hz'
      simp [G, hz']
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : z ∈ O
    · exact hOn.continuousAt (hO.mem_nhds hz)
    · have hGz : G z = p := by
        have hz' : z.1 ∉ OpenInterval := hz
        exact dite_eq_right hz'
      have hJcompact (R : ℝ) :
          IsCompact ((fun t : ℝ => (r t : CurveComplex.Interval)) '' Set.Icc (-R) R) :=
        isCompact_Icc.image (continuous_subtype_val.comp r.continuous)
      rw [ContinuousAt, hGz]
      intro V hV
      obtain ⟨V', hV'V, hV'open, hpV'⟩ := mem_nhds_iff.mp hV
      obtain ⟨R, hR⟩ := proper_strip_uniform_ends_at_puncture' p F hF V' hV'open hpV'
      let J : Set CurveComplex.Interval :=
        (fun t : ℝ => (r t : CurveComplex.Interval)) '' Set.Icc (-R) R
      have hJ : IsClosed J := (hJcompact R).isClosed
      have hzJ : z.1 ∉ J := by
        rintro ⟨t, ht, he⟩
        exact hz (show z.1 ∈ OpenInterval from by
          exact (he ▸ (r t).property))
      have hnear : {y : CurveComplex.Interval × W | y.1 ∉ J} ∈ 𝓝 z :=
        (hJ.isOpen_compl.preimage continuous_fst).mem_nhds hzJ
      apply Filter.mem_of_superset hnear
      intro y hy
      change G y ∈ V
      by_cases hys : y.1 ∈ OpenInterval
      · have hbound : R ≤ |r.symm ⟨y.1, hys⟩| := by
          by_contra hnot
          have hlt : |r.symm ⟨y.1, hys⟩| < R := lt_of_not_ge hnot
          have hmem : r.symm ⟨y.1, hys⟩ ∈ Set.Icc (-R) R := by
            constructor <;> linarith [abs_le.mp hlt.le]
          apply hy
          exact ⟨r.symm ⟨y.1, hys⟩, hmem, congrArg Subtype.val (r.apply_symm_apply _)⟩
        change (if hs : y.1 ∈ OpenInterval then
          (F (r.symm ⟨y.1, hs⟩, y.2)).val else p) ∈ V
        rw [dite_eq_left hys]
        exact hV'V (hR (r.symm ⟨y.1, hys⟩) y.2 hbound)
      · change (if hs : y.1 ∈ OpenInterval then
          (F (r.symm ⟨y.1, hs⟩, y.2)).val else p) ∈ V
        rw [dite_eq_right hys]
        exact hV'V hpV'
  exact ⟨G, hG⟩

theorem properStripCompactification_interior
    {X W : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace W] (p : X)
    (F : C(ℝ × W, {x : X // x ≠ p})) (hF : IsProperMap F)
    (r : ℝ ≃ₜ OpenInterval) (s : CurveComplex.Interval) (w : W)
    (hs : s ∈ OpenInterval) :
    properStripCompactification p F hF r (s, w) =
      (F (r.symm ⟨s, hs⟩, w)).val := by
  have hs' : (0 : CurveComplex.Interval) < s ∧ s < 1 := hs
  change (if h : (0 : CurveComplex.Interval) < s ∧ s < 1 then
    (F (r.symm ⟨s, h⟩, w)).val else p) = _
  rw [dite_eq_left hs']

theorem properStripCompactification_ends
    {X W : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace W] (p : X)
    (F : C(ℝ × W, {x : X // x ≠ p})) (hF : IsProperMap F)
    (r : ℝ ≃ₜ OpenInterval) (w : W) :
    properStripCompactification p F hF r (0, w) = p ∧
      properStripCompactification p F hF r (1, w) = p := by
  constructor <;> simp [properStripCompactification, OpenInterval]

theorem properStripCompactification_injective_except_ends
    {X W : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace W] (p : X)
    (F : C(ℝ × W, {x : X // x ≠ p})) (hF : IsProperMap F)
    (hFI : Function.Injective F) (r : ℝ ≃ₜ OpenInterval)
    (s s' : CurveComplex.Interval) (w w' : W)
    (he : properStripCompactification p F hF r (s, w) =
      properStripCompactification p F hF r (s', w')) :
    (s = s' ∧ w = w') ∨
      ((s = 0 ∨ s = 1) ∧ (s' = 0 ∨ s' = 1)) := by
  have hedge (x : CurveComplex.Interval) (hx : x ∉ OpenInterval) :
      x = 0 ∨ x = 1 := by
    simp only [OpenInterval, Set.mem_Ioo, not_and_or, not_lt] at hx
    rcases hx with h0 | h1
    · left
      exact le_antisymm h0 x.property.1
    · right
      exact le_antisymm x.property.2 h1
  by_cases hs : s ∈ OpenInterval
  · by_cases hs' : s' ∈ OpenInterval
    · left
      have he' : F (r.symm ⟨s, hs⟩, w) = F (r.symm ⟨s', hs'⟩, w') :=
        Subtype.ext (by simpa [properStripCompactification_interior p F hF r s w hs,
          properStripCompactification_interior p F hF r s' w' hs'] using he)
      have hpair := hFI he'
      constructor
      · have hparam : (⟨s, hs⟩ : OpenInterval) = ⟨s', hs'⟩ :=
          r.symm.injective (congrArg Prod.fst hpair)
        exact congrArg Subtype.val hparam
      · exact congrArg Prod.snd hpair
    · have hnot : properStripCompactification p F hF r (s, w) ≠ p := by
        rw [properStripCompactification_interior p F hF r s w hs]
        exact (F (r.symm ⟨s, hs⟩, w)).property
      have hother : properStripCompactification p F hF r (s', w') = p := by
        have hs'' : ¬ ((0 : CurveComplex.Interval) < s' ∧ s' < 1) := hs'
        change (if h : (0 : CurveComplex.Interval) < s' ∧ s' < 1 then
          (F (r.symm ⟨s', h⟩, w')).val else p) = p
        exact dite_eq_right hs''
      exact False.elim (hnot (he.trans hother))
  · by_cases hs' : s' ∈ OpenInterval
    · have hnot : properStripCompactification p F hF r (s', w') ≠ p := by
        rw [properStripCompactification_interior p F hF r s' w' hs']
        exact (F (r.symm ⟨s', hs'⟩, w')).property
      have hother : properStripCompactification p F hF r (s, w) = p := by
        have hs'' : ¬ ((0 : CurveComplex.Interval) < s ∧ s < 1) := hs
        change (if h : (0 : CurveComplex.Interval) < s ∧ s < 1 then
          (F (r.symm ⟨s, h⟩, w)).val else p) = p
        exact dite_eq_right hs''
      exact False.elim (hnot (he.symm.trans hother))
    · exact Or.inr ⟨hedge s hs, hedge s' hs'⟩
