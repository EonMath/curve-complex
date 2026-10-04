import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches

open CurveComplex Set Topology

/-- Two arbitrarily close parallel proper arcs inside a prescribed regional
    neighborhood, obtained from an actual embedded proper strip in `F`. -/
theorem regional_embedded_proper_strip_two_supported_push_offs
    {S : Type} [TopologicalSpace S] [T2Space S]
    (F B : Set S) (a : C(Interval, ↥F))
    (E : C(Interval × Set.Icc (-1 : ℝ) 1, ↥F))
    (hE : Topology.IsEmbedding E)
    (hcenter : ∀ t, E (t, ⟨0, by norm_num⟩) = a t)
    (hend : ∀ w, (E (0,w)).val ∈ B ∧ (E (1,w)).val ∈ B)
    (hint : ∀ t ∈ Set.Ioo (0 : Interval) 1, ∀ w,
      (E (t,w)).val ∉ frontier F)
    (O : Set ↥F) (hO : IsOpen O) (haO : Set.range a ⊆ O) :
    ∃ p q : C(Interval, ↥F),
      Topology.IsEmbedding p ∧ Topology.IsEmbedding q ∧
      (p 0).val ∈ B ∧ (p 1).val ∈ B ∧
      (q 0).val ∈ B ∧ (q 1).val ∈ B ∧
      (∀ t ∈ Set.Ioo (0 : Interval) 1, (p t).val ∉ frontier F) ∧
      (∀ t ∈ Set.Ioo (0 : Interval) 1, (q t).val ∉ frontier F) ∧
      Set.range p ⊆ O ∧ Set.range q ⊆ O ∧
      Disjoint (Set.range p) (Set.range a) ∧
      Disjoint (Set.range q) (Set.range a) ∧
      Disjoint (Set.range p) (Set.range q) ∧
      ∃ wp wm : Set.Icc (-1 : ℝ) 1,
        (∀ t, p t = E (t,wp)) ∧ (∀ t, q t = E (t,wm)) := by
  let zero : Set.Icc (-1 : ℝ) 1 := ⟨0, by norm_num⟩
  have hprod : ({zero} : Set (Set.Icc (-1 : ℝ) 1)) ×ˢ Set.univ ⊆
      (fun z : Set.Icc (-1 : ℝ) 1 × Interval => E (z.2,z.1)) ⁻¹' O := by
    rintro ⟨w,t⟩ ⟨hw,ht⟩
    obtain rfl := Set.mem_singleton_iff.mp hw
    change E (t,zero) ∈ O
    rw [hcenter]
    exact haO (Set.mem_range_self t)
  obtain ⟨U,V,hU,hV,hzero,hI,hUV⟩ := generalized_tube_lemma
    isCompact_singleton isCompact_univ
    (hO.preimage (hE.continuous.comp continuous_swap)) hprod
  obtain ⟨ε,hε,hεU⟩ := Metric.isOpen_iff.mp hU zero (hzero (Set.mem_singleton _))
  let δ : ℝ := min (ε/2) (1/2)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  let wp : Set.Icc (-1 : ℝ) 1 := ⟨δ, by constructor <;> linarith [min_le_right (ε/2) (1/2)]⟩
  let wm : Set.Icc (-1 : ℝ) 1 := ⟨-δ, by constructor <;> linarith [min_le_right (ε/2) (1/2)]⟩
  let p : C(Interval, ↥F) :=
    ⟨fun t => E (t,wp), hE.continuous.comp (continuous_id.prodMk continuous_const)⟩
  let q : C(Interval, ↥F) :=
    ⟨fun t => E (t,wm), hE.continuous.comp (continuous_id.prodMk continuous_const)⟩
  have hp : Topology.IsEmbedding p :=
    (p.continuous.isClosedEmbedding (by
      intro s t he
      exact congrArg Prod.fst (hE.injective he))).isEmbedding
  have hq : Topology.IsEmbedding q :=
    (q.continuous.isClosedEmbedding (by
      intro s t he
      exact congrArg Prod.fst (hE.injective he))).isEmbedding
  have hside (w : Set.Icc (-1 : ℝ) 1) (hw : |(w : ℝ)| < ε) :
      ∀ t : Interval, E (t,w) ∈ O := by
    intro t
    apply hUV (show (w,t) ∈ U ×ˢ V from ?_)
    constructor
    · apply hεU
      change dist (w : ℝ) 0 < ε
      simpa only [Real.dist_eq,sub_zero] using hw
    · exact hI (Set.mem_univ t)
  have hpO : Set.range p ⊆ O := by
    rintro _ ⟨t,rfl⟩
    exact hside wp (by simpa only [wp,Subtype.coe_mk,abs_of_pos hδ] using hδε) t
  have hqO : Set.range q ⊆ O := by
    rintro _ ⟨t,rfl⟩
    exact hside wm (by simpa only [wm,Subtype.coe_mk,abs_neg,abs_of_pos hδ] using hδε) t
  have hdisjCenter (b : C(Interval, ↥F)) (w : Set.Icc (-1 : ℝ) 1)
      (hb : ∀ t, b t = E (t,w)) (hw : (w : ℝ) ≠ 0) :
      Disjoint (Set.range b) (Set.range a) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨t,rfl⟩ ⟨u,hu⟩
    have he : E (u,zero) = E (t,w) := (hcenter u).trans (hu.trans (hb t))
    have hh := congrArg (fun z : Interval × Set.Icc (-1 : ℝ) 1 => (z.2 : ℝ))
      (hE.injective he)
    exact hw hh.symm
  refine ⟨p,q,hp,hq,(hend wp).1,(hend wp).2,(hend wm).1,(hend wm).2,
    (fun t ht => hint t ht wp),(fun t ht => hint t ht wm),hpO,hqO,
    hdisjCenter p wp (fun t => rfl) hδ.ne',
    hdisjCenter q wm (fun t => rfl) (by change -δ ≠ 0; linarith),?_,
    ⟨wp,wm,fun t => rfl,fun t => rfl⟩⟩
  · apply Set.disjoint_left.mpr
    rintro y ⟨t,rfl⟩ ⟨u,hu⟩
    have he : E (u,wm) = E (t,wp) := hu.trans rfl
    have hh := congrArg (fun z : Interval × Set.Icc (-1 : ℝ) 1 => (z.2 : ℝ))
      (hE.injective he)
    change -δ = δ at hh
    linarith

#print axioms regional_embedded_proper_strip_two_supported_push_offs

/-- Sliding a proper arc to any fixed width in an embedded regional strip is
    an explicit family of embedded proper arcs, with both endpoint tracks in
    the distinguished boundary. -/
theorem regional_embedded_strip_constant_width_family
    {S : Type} [TopologicalSpace S] [T2Space S]
    (F B : Set S) (a : C(Interval, ↥F))
    (E : C(Interval × Set.Icc (-1 : ℝ) 1, ↥F))
    (hE : Topology.IsEmbedding E)
    (hcenter : ∀ t, E (t,⟨0,by norm_num⟩) = a t)
    (hend : ∀ w, (E (0,w)).val ∈ B ∧ (E (1,w)).val ∈ B)
    (hint : ∀ t ∈ Set.Ioo (0 : Interval) 1, ∀ w,
      (E (t,w)).val ∉ frontier F)
    (w : Set.Icc (-1 : ℝ) 1) :
    ∃ H : C(Interval × Interval, ↥F),
      (∀ t, H (0,t) = a t) ∧
      (∀ t, H (1,t) = E (t,w)) ∧
      (∀ s, Topology.IsEmbedding (fun t : Interval => H (s,t))) ∧
      (∀ s, (H (s,0)).val ∈ B ∧ (H (s,1)).val ∈ B) ∧
      (∀ s t, t ∈ Set.Ioo (0 : Interval) 1 →
        (H (s,t)).val ∉ frontier F) := by
  let width (s : Interval) : Set.Icc (-1 : ℝ) 1 :=
    ⟨s.val * w.val, by
      have hlo := mul_le_mul_of_nonneg_left w.property.1 s.property.1
      have hhi := mul_le_mul_of_nonneg_left w.property.2 s.property.1
      constructor <;> nlinarith [s.property.2]⟩
  have hwidth : Continuous width := by
    apply Continuous.subtype_mk
    fun_prop
  let H : C(Interval × Interval,↥F) :=
    ⟨fun z => E (z.2,width z.1),
      E.continuous.comp (continuous_snd.prodMk (hwidth.comp continuous_fst))⟩
  refine ⟨H,?_,?_,?_,?_,?_⟩
  · intro t
    change E (t,width 0) = a t
    simpa [width] using hcenter t
  · intro t
    change E (t,width 1) = E (t,w)
    have hw : width 1 = w := by
      apply Subtype.ext
      simp [width]
    rw [hw]
  · intro s
    exact ((show Continuous (fun t : Interval => H (s,t)) from by fun_prop).isClosedEmbedding
      (by intro t u he
          exact congrArg Prod.fst (hE.injective he))).isEmbedding
  · intro s
    exact hend (width s)
  · intro s t ht
    exact hint t ht (width s)

#print axioms regional_embedded_strip_constant_width_family
