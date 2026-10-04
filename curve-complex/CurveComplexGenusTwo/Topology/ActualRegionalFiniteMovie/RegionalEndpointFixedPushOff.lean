import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalCleanDiskFamily

open CurveComplex Set Topology

namespace RegionalEmbeddedFamily

private noncomputable def taperedWidth (s : Interval) : Set.Icc (-1 : ℝ) 1 :=
  ⟨(s : ℝ) * (1 - (s : ℝ)) / 2, by
    constructor
    · have h0 : 0 ≤ (s : ℝ) := s.property.1
      have h1 : (s : ℝ) ≤ 1 := s.property.2
      have hp : 0 ≤ (s : ℝ) * (1 - (s : ℝ)) := mul_nonneg h0 (by linarith)
      linarith
    · have h0 : 0 ≤ (s : ℝ) := s.property.1
      have h1 : (s : ℝ) ≤ 1 := s.property.2
      have hp : (s : ℝ) * (1 - (s : ℝ)) ≤ 1 := by nlinarith
      linarith⟩

private theorem taperedWidth_continuous : Continuous taperedWidth := by
  apply Continuous.subtype_mk
  fun_prop

private theorem taperedWidth_zero : taperedWidth 0 = ⟨0, by norm_num⟩ :=
  Subtype.ext (by norm_num [taperedWidth])

private theorem taperedWidth_one : taperedWidth 1 = ⟨0, by norm_num⟩ :=
  Subtype.ext (by norm_num [taperedWidth])

private theorem taperedWidth_pos {s : Interval}
    (hs : s ∈ Set.Ioo (0 : Interval) 1) :
    (0 : ℝ) < (taperedWidth s).val := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs.1
  have hs1 : (s : ℝ) < 1 := by exact_mod_cast hs.2
  change 0 < (s : ℝ) * (1 - (s : ℝ)) / 2
  positivity

theorem embedded_strip_tapered_fixed_endpoint_push_off
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (F : Set S) (a : C(Interval, ↥F))
    (E : C(Interval × Set.Icc (-1 : ℝ) 1, ↥F))
    (hE : Topology.IsEmbedding E)
    (hcenter : ∀ s, E (s, ⟨0, by norm_num⟩) = a s)
    (hint : ∀ s ∈ Set.Ioo (0 : Interval) 1, ∀ w,
      (E (s,w)).val ∉ frontier F) :
    ∃ (q : C(Interval, ↥F)) (H : C(Interval × Interval, ↥F)),
      Topology.IsEmbedding q ∧
      q 0 = a 0 ∧ q 1 = a 1 ∧
      (∀ s ∈ Set.Ioo (0 : Interval) 1,
        (q s).val ∉ frontier F) ∧
      (∀ s t, a s = q t →
        (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) ∧
      (∀ s, H (0,s) = a s ∧ H (1,s) = q s) ∧
      (∀ t, Topology.IsEmbedding (fun s => H (t,s))) ∧
      (∀ t, H (t,0) = a 0 ∧ H (t,1) = a 1) ∧
      (∀ t s, s ∈ Set.Ioo (0 : Interval) 1 →
        (H (t,s)).val ∉ frontier F) := by
  let width (t s : Interval) : Set.Icc (-1 : ℝ) 1 :=
    ⟨(t : ℝ) * (taperedWidth s).val, by
      have ht0 : 0 ≤ (t : ℝ) := t.property.1
      have ht1 : (t : ℝ) ≤ 1 := t.property.2
      have hw0 : 0 ≤ (taperedWidth s).val := by
        change 0 ≤ (s : ℝ) * (1 - (s : ℝ)) / 2
        have hs0 : 0 ≤ (s : ℝ) := s.property.1
        have hs1 : (s : ℝ) ≤ 1 := s.property.2
        positivity
      have hw1 : (taperedWidth s).val ≤ 1 := (taperedWidth s).property.2
      constructor
      · nlinarith
      · nlinarith⟩
  have hwidth : Continuous (fun p : Interval × Interval =>
      width p.1 p.2) := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp
        (taperedWidth_continuous.comp continuous_snd))
  let H : C(Interval × Interval, ↥F) :=
    ⟨fun p => E (p.2, width p.1 p.2),
      E.continuous.comp (continuous_snd.prodMk hwidth)⟩
  let q : C(Interval, ↥F) :=
    ⟨fun s => H (1,s), H.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hwidth0 (s : Interval) : width 0 s = ⟨0, by norm_num⟩ :=
    Subtype.ext (by simp [width])
  have hwidth1 (s : Interval) : width 1 s = taperedWidth s :=
    Subtype.ext (by simp [width])
  have hH0 (s : Interval) : H (0,s) = a s := by
    change E (s, width 0 s) = a s
    rw [hwidth0]
    exact hcenter s
  have hH1 (s : Interval) : H (1,s) = q s := rfl
  have hemb (t : Interval) : Topology.IsEmbedding (fun s => H (t,s)) := by
    have hc : Continuous (fun s : Interval => H (t,s)) :=
      H.continuous.comp (continuous_const.prodMk continuous_id)
    have hi : Function.Injective (fun s => H (t,s)) := by
      intro s u he
      exact congrArg Prod.fst (hE.injective he)
    exact (hc.isClosedEmbedding hi).isEmbedding
  have hq : Topology.IsEmbedding q := hemb 1
  have hq0 : q 0 = a 0 := by
    change E (0, width 1 0) = a 0
    rw [hwidth1, taperedWidth_zero]
    exact hcenter 0
  have hq1 : q 1 = a 1 := by
    change E (1, width 1 1) = a 1
    rw [hwidth1, taperedWidth_one]
    exact hcenter 1
  have hqclear (s : Interval) (hs : s ∈ Set.Ioo (0 : Interval) 1) :
      (q s).val ∉ frontier F := hint s hs _
  have hmeet (s t : Interval) (hst : a s = q t) :
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    have he : E (s, ⟨0, by norm_num⟩) =
        E (t, width 1 t) := (hcenter s).trans hst
    have hp := hE.injective he
    have hst' : s = t := congrArg Prod.fst hp
    have hw : (0 : ℝ) = (taperedWidth t).val := by
      have hpw := congrArg (fun z : Interval × Set.Icc (-1 : ℝ) 1 =>
        (z.2 : ℝ)) hp
      simpa only [hwidth1] using hpw
    by_cases ht0 : t = 0
    · left
      exact ⟨hst'.trans ht0, ht0⟩
    have ht0' : (0 : ℝ) < t := lt_of_le_of_ne t.property.1
      (fun he => ht0 (Subtype.ext he.symm))
    have ht1 : t = 1 := by
      by_contra hn
      have ht1' : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2
        (fun he => hn (Subtype.ext he))
      exact (ne_of_lt (taperedWidth_pos ⟨ht0', ht1'⟩)) hw
    right
    exact ⟨hst'.trans ht1, ht1⟩
  refine ⟨q, H, hq, hq0, hq1, hqclear, hmeet, ?_, hemb, ?_, ?_⟩
  · intro s
    exact ⟨hH0 s, hH1 s⟩
  · intro t
    constructor
    · change E (0, width t 0) = a 0
      have hw : width t 0 = ⟨0, by norm_num⟩ := by
        apply Subtype.ext
        simp [width, taperedWidth]
      rw [hw]
      exact hcenter 0
    · change E (1, width t 1) = a 1
      have hw : width t 1 = ⟨0, by norm_num⟩ := by
        apply Subtype.ext
        simp [width, taperedWidth]
      rw [hw]
      exact hcenter 1
  · intro t s hs
    exact hint s hs (width t s)

end RegionalEmbeddedFamily
