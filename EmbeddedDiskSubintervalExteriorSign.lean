import CurveComplexGenusTwo.Foundations.Definitions
import Schoenflies.Square
import Mathlib.Topology.OpenPartialHomeomorph.Defs

open CurveComplex Set Topology Schoenflies
set_option autoImplicit false

theorem embedded_disk_subinterval_edge_has_uniform_exterior_sign
    {X : Type} [TopologicalSpace X] [T2Space X]
    (P : C(Interval × Interval, X)) (hP : IsEmbedding P)
    (E : C(Interval × Set.Icc (-1 : ℝ) 1, X)) (hE : IsEmbedding E)
    (j : C(Interval, Interval))
    (hseam : ∀ s : Interval, P (s, 0) = E (j s, ⟨0, by norm_num⟩))
    (hwhole : Set.range P ∩
      Set.range (fun t : Interval => E (t, ⟨0, by norm_num⟩)) =
      Set.range (fun s : Interval => P (s, 0)))
    (hopen : IsOpen (E '' {z | -1 < z.2.val ∧ z.2.val < 1})) :
    ∃ σ ρ : ℝ, (σ = -1 ∨ σ = 1) ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ t ∈ Set.range j, ∀ u : Set.Icc (-1 : ℝ) 1,
        0 < σ * u.val → σ * u.val ≤ ρ → E (t, u) ∉ Set.range P := by
  let U : Set X := E '' {z | -1 < z.2.val ∧ z.2.val < 1}
  have hprod : (univ : Set Interval) ×ˢ ({0} : Set Interval) ⊆ P ⁻¹' U := by
    rintro ⟨s,w⟩ ⟨_,hw⟩
    obtain rfl := mem_singleton_iff.mp hw
    exact ⟨(j s,⟨0,by norm_num⟩),by norm_num,(hseam s).symm⟩
  obtain ⟨A,V,hA,hV,hIA,h0V,hAV⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton
      (hopen.preimage P.continuous) hprod
  obtain ⟨r,hr,hrV⟩ := Metric.isOpen_iff.mp hV 0 (h0V (mem_singleton _))
  let δ : ℝ := min (r/2) (1/2)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ1 : δ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hδr : δ < r := (min_le_left _ _).trans_lt (by linarith)
  let scale : Interval × Interval → Interval × Interval := fun z =>
    (z.1,⟨δ*(z.2:ℝ),by constructor <;> nlinarith [z.2.property.1,z.2.property.2,hδ,hδ1]⟩)
  have hsc : Continuous scale := by dsimp [scale]; fun_prop
  have hthin (z : Interval × Interval) : P (scale z) ∈ U := by
    apply hAV
    refine ⟨hIA (mem_univ _),hrV ?_⟩
    rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq]
    change |δ*(z.2:ℝ)-0| < r
    rw [sub_zero,abs_of_nonneg (mul_nonneg hδ.le z.2.property.1)]
    exact (mul_le_of_le_one_right hδ.le z.2.property.2).trans_lt hδr
  let e := hE.toHomeomorph
  let k : C(Interval × Interval,Interval × Icc (-1:ℝ) 1) :=
    ⟨fun z => e.symm ⟨P (scale z),image_subset_range E _ (hthin z)⟩,
      e.symm.continuous.comp ((P.continuous.comp hsc).subtype_mk _)⟩
  have hEk (z) : E (k z) = P (scale z) :=
    congrArg Subtype.val (e.apply_symm_apply _)
  have hn (z : Interval × Interval) (hz : 0 < z.2) : ((k z).2:ℝ) ≠ 0 := by
    intro he
    have hw : (k z).2 = (⟨0,by norm_num⟩ : Icc (-1:ℝ) 1) := Subtype.ext he
    have hm : P (scale z) ∈ range P ∩
        range (fun t : Interval => E (t,⟨0,by norm_num⟩)) := by
      refine ⟨mem_range_self _,⟨(k z).1,?_⟩⟩
      exact (congrArg E (show ((k z).1,⟨0,by norm_num⟩) = k z from
        Prod.ext rfl hw.symm)).trans (hEk z)
    rw [hwhole] at hm
    obtain ⟨s,hs⟩ := hm
    have hh := congrArg (fun z : Interval × Interval => (z.2:ℝ)) (hP.injective hs)
    change 0 = δ*(z.2:ℝ) at hh
    have hz' : (0:ℝ) < z.2 := hz
    exact (mul_pos hδ hz').ne' hh.symm
  have hp : IsPreconnected ((univ : Set Interval) ×ˢ Ioi (0:Interval)) :=
    isPreconnected_univ.prod isPreconnected_Ioi
  have hside := hp.mapsTo_Ioi_or_Iio
    (show Continuous (fun z => ((k z).2:ℝ)) from
      continuous_subtype_val.comp (continuous_snd.comp k.continuous)).continuousOn
    (fun z hz => hn z hz.2)
  let F : Set X := P '' {z | δ ≤ (z.2:ℝ)}
  have hF : IsClosed F := ((isClosed_le continuous_const
    (continuous_subtype_val.comp continuous_snd)).isCompact.image P.continuous).isClosed
  have hcenterF (t : Interval) (ht : t ∈ range j) : E (t,⟨0,by norm_num⟩) ∉ F := by
    obtain ⟨s,rfl⟩ := ht
    rw [← hseam]
    rintro ⟨z,hz,he⟩
    have hh := congrArg (fun z : Interval × Interval => (z.2:ℝ)) (hP.injective he)
    change (z.2:ℝ) = 0 at hh
    change δ ≤ (z.2:ℝ) at hz
    rw [hh] at hz
    linarith
  have hprodF : range j ×ˢ ({⟨0,by norm_num⟩} : Set (Icc (-1:ℝ) 1)) ⊆ E ⁻¹' Fᶜ := by
    rintro ⟨t,u⟩ ⟨ht,hu⟩
    obtain rfl := mem_singleton_iff.mp hu
    exact hcenterF t ht
  obtain ⟨A',V',hA',hV',hJA',h0V',hAV'⟩ :=
    generalized_tube_lemma (isCompact_range j.continuous) isCompact_singleton
      (hF.isOpen_compl.preimage E.continuous) hprodF
  obtain ⟨r',hr',hrV'⟩ := Metric.isOpen_iff.mp hV' ⟨0,by norm_num⟩
    (h0V' (mem_singleton _))
  let ρ : ℝ := min (r'/2) (1/2)
  have hρ : 0 < ρ := lt_min (by positivity) (by norm_num)
  have hρ1 : ρ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hρr : ρ < r' := (min_le_left _ _).trans_lt (by linarith)
  have hnear (t : Interval) (ht : t ∈ range j) (u : Icc (-1:ℝ) 1)
      (hu : |u.val| ≤ ρ) : E (t,u) ∉ F := by
    apply hAV'
    refine ⟨hJA' ht,hrV' ?_⟩
    rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq]
    change |u.val-0| < r'
    rw [sub_zero]
    exact hu.trans_lt hρr
  have build (σ : ℝ) (hσ : σ = -1 ∨ σ = 1)
      (hopp : ∀ z, 0 < z.2 → σ*((k z).2:ℝ) < 0) :
      ∀ t ∈ range j, ∀ u : Icc (-1:ℝ) 1,
        0 < σ*u.val → σ*u.val ≤ ρ → E (t,u) ∉ range P := by
    intro t ht u hu huρ hmeet
    have huabs : |u.val| ≤ ρ := by
      rcases hσ with rfl | rfl
      · rw [abs_of_neg (by linarith : u.val < 0)]; linarith
      · rw [abs_of_pos (by linarith : 0 < u.val)]; simpa using huρ
    obtain ⟨v,hv⟩ := hmeet
    have hvδ : (v.2:ℝ) < δ := lt_of_not_ge (fun hh =>
      (hnear t ht u huabs) ⟨v,hh,hv⟩)
    let w : Interval := ⟨(v.2:ℝ)/δ,⟨div_nonneg v.2.property.1 hδ.le,
      (div_le_one hδ).mpr hvδ.le⟩⟩
    have hs : scale (v.1,w) = v := by
      apply Prod.ext
      · rfl
      apply Subtype.ext
      change δ*((v.2:ℝ)/δ) = (v.2:ℝ)
      field_simp [hδ.ne']
    have he : E (k (v.1,w)) = E (t,u) :=
      (hEk _).trans ((congrArg P hs).trans hv)
    have hk := congrArg (fun z : Interval × Icc (-1:ℝ) 1 => (z.2:ℝ)) (hE.injective he)
    by_cases hw0 : v.2 = 0
    · have hv0 : v = (v.1,0) := Prod.ext rfl hw0
      have he' : E (t,u) = E (j v.1,⟨0,by norm_num⟩) :=
        hv.symm.trans ((congrArg P hv0).trans (hseam v.1))
      have hh := congrArg (fun z : Interval × Icc (-1:ℝ) 1 => (z.2:ℝ)) (hE.injective he')
      change u.val = 0 at hh
      rw [hh,mul_zero] at hu
      exact lt_irrefl 0 hu
    · have hvpos : (0:ℝ) < v.2 := lt_of_le_of_ne v.2.property.1
        (fun he => hw0 (Subtype.ext he.symm))
      have hwpos : (0:Interval) < w := div_pos hvpos hδ
      have hh := hopp (v.1,w) hwpos
      rw [hk] at hh
      exact not_lt_of_ge hu.le hh
  rcases hside with hside | hside
  · refine ⟨-1,ρ,Or.inl rfl,hρ,hρ1,build (-1) (Or.inl rfl) ?_⟩
    intro z hz
    have hh := hside ⟨mem_univ _,hz⟩
    change 0 < ((k z).2:ℝ) at hh
    linarith
  · refine ⟨1,ρ,Or.inr rfl,hρ,hρ1,build 1 (Or.inr rfl) ?_⟩
    intro z hz
    have hh := hside ⟨mem_univ _,hz⟩
    change ((k z).2:ℝ) < 0 at hh
    simpa only [one_mul] using hh
