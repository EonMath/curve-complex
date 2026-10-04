import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalRelativeSupportNeighborhood

open CurveComplex Set Topology

/-- Uniformly narrow a whole proper strip so all fibers over a compact active
parameter set lie in the prescribed open support. Other fibers need not lie there. -/
private theorem half_strip_active_compact_narrowing
    {S : Type} [TopologicalSpace S] [T2Space S]
    (F B : Set S)
    (E : C(Interval × Set.Icc (-1 : ℝ) 1,↥F))
    (hE : Topology.IsEmbedding E)
    (hend : ∀ w, (E (0,w)).val ∈ B ∧ (E (1,w)).val ∈ B)
    (hint : ∀ t ∈ Set.Ioo (0 : Interval) 1, ∀ w,
      (E (t,w)).val ∈ interior F)
    (hopen : IsOpen (E '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}))
    (A : Set Interval) (hA : IsCompact A)
    (V : Set ↥F) (hV : IsOpen V)
    (hcenterV : ∀ t ∈ A, E (t,⟨0,by norm_num⟩) ∈ V) :
    ∃ N : C(Interval × Set.Icc (-1 : ℝ) 1,↥F), ∃ W : Set Interval,
      IsOpen W ∧ A ⊆ W ∧ Topology.IsEmbedding N ∧
      (∀ t, N (t,⟨0,by norm_num⟩) = E (t,⟨0,by norm_num⟩)) ∧
      (∀ t ∈ W, ∀ w, N (t,w) ∈ V) ∧
      (∀ w, (N (0,w)).val ∈ B ∧ (N (1,w)).val ∈ B) ∧
      (∀ t ∈ Set.Ioo (0 : Interval) 1, ∀ w,
        (N (t,w)).val ∈ interior F) ∧
      IsOpen (N '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}) := by
  let zero : Set.Icc (-1 : ℝ) 1 := ⟨0,by norm_num⟩
  have hprod : ({zero} : Set (Set.Icc (-1 : ℝ) 1)) ×ˢ A ⊆
      (fun z : Set.Icc (-1 : ℝ) 1 × Interval => E (z.2,z.1)) ⁻¹' V := by
    rintro ⟨w,t⟩ ⟨hw,ht⟩
    obtain rfl := Set.mem_singleton_iff.mp hw
    exact hcenterV t ht
  obtain ⟨U,W,hU,hW,hzero,hAW,hUW⟩ := generalized_tube_lemma
    isCompact_singleton hA
    (hV.preimage (E.continuous.comp continuous_swap)) hprod
  obtain ⟨δ,hδ,hδU⟩ := Metric.isOpen_iff.mp hU zero
    (hzero (Set.mem_singleton _))
  let ρ : ℝ := min δ 1 / 2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρδ : ρ < δ := by dsimp [ρ]; linarith [min_le_left δ 1]
  have hρ1 : ρ ≤ 1 := by dsimp [ρ]; linarith [min_le_right δ 1]
  let scale : Set.Icc (-1 : ℝ) 1 → Set.Icc (-1 : ℝ) 1 := fun w =>
    ⟨ρ * (w : ℝ),by
      constructor <;> nlinarith [w.property.1,w.property.2,hρ,hρ1]⟩
  let N : C(Interval × Set.Icc (-1 : ℝ) 1,↥F) :=
    ⟨fun z => E (z.1,scale z.2),by dsimp [scale]; fun_prop⟩
  have hN : Topology.IsEmbedding N :=
    (N.continuous.isClosedEmbedding (by
      intro z u he
      have hp := hE.injective he
      apply Prod.ext
      · have ht := congrArg (fun z : Interval × Set.Icc (-1 : ℝ) 1 => z.1) hp
        exact ht
      · apply Subtype.ext
        have hw := congrArg (fun z : Interval × Set.Icc (-1 : ℝ) 1 =>
          (z.2 : ℝ)) hp
        change ρ * (z.2 : ℝ) = ρ * (u.2 : ℝ) at hw
        exact (mul_left_cancel₀ (ne_of_gt hρ) hw))).isEmbedding
  refine ⟨N,W,hW,hAW,hN,?_,?_,?_,?_,?_⟩
  · intro t
    change E (t,scale zero) = E (t,zero)
    have hs : scale zero = zero := Subtype.ext (by simp [scale,zero])
    rw [hs]
  · intro t ht w
    apply hUW (show (scale w,t) ∈ U ×ˢ W from ⟨?_,ht⟩)
    apply hδU
    change dist (ρ * (w : ℝ)) 0 < δ
    rw [Real.dist_eq,sub_zero,abs_mul,abs_of_pos hρ]
    have hw : |(w : ℝ)| ≤ 1 := abs_le.mpr w.property
    exact (mul_le_mul_of_nonneg_left hw hρ.le).trans_lt
      (by simpa using hρδ)
  · intro w
    exact hend (scale w)
  · intro t ht w
    exact hint t ht (scale w)
  · apply regional_strip_narrow_open_core F F (Set.Subset.rfl) E hE hopen ρ hρ hρ1 N
    intro z
    rfl

#print axioms half_strip_active_compact_narrowing
