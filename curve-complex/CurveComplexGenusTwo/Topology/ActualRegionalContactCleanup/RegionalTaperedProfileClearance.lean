import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalProperProfileAmbientMove

open CurveComplex Set Topology

/-- Uniform transverse clearance over an arbitrary compact parameter set. -/
theorem regional_strip_compact_parameter_clearance
    {X : Type} [TopologicalSpace X] [T2Space X]
    (E : C(Interval × Set.Icc (-1 : ℝ) 1,X))
    (A : Set Interval) (hA : IsCompact A)
    (K : Set X) (hK : IsClosed K)
    (hclear : ∀ t ∈ A, E (t,⟨0,by norm_num⟩) ∉ K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ A,
      ∀ w : Set.Icc (-1 : ℝ) 1, |(w : ℝ)| < δ → E (t,w) ∉ K := by
  let zero : Set.Icc (-1 : ℝ) 1 := ⟨0,by norm_num⟩
  have hprod : ({zero} : Set (Set.Icc (-1 : ℝ) 1)) ×ˢ A ⊆
      (fun z : Set.Icc (-1 : ℝ) 1 × Interval => E (z.2,z.1)) ⁻¹' Kᶜ := by
    rintro ⟨w,t⟩ ⟨hw,ht⟩
    obtain rfl := Set.mem_singleton_iff.mp hw
    exact hclear t ht
  obtain ⟨U,W,hU,hW,hzero,hAW,hUW⟩ := generalized_tube_lemma
    isCompact_singleton hA
    (hK.isOpen_compl.preimage (E.continuous.comp continuous_swap)) hprod
  obtain ⟨δ,hδ,hδU⟩ := Metric.isOpen_iff.mp hU zero
    (hzero (Set.mem_singleton _))
  refine ⟨δ,hδ,?_⟩
  intro t ht w hw
  have hwU : w ∈ U := by
    apply hδU
    change dist (w : ℝ) 0 < δ
    simpa only [Real.dist_eq,sub_zero] using hw
  exact hUW (show (w,t) ∈ U ×ˢ W from ⟨hwU,hAW ht⟩)

/-- Local positive-side clearance at the only center contact yields a
    continuous displacement positive before q and zero on the retained tail. -/
theorem regional_tapered_profile_avoids_prefix_obstacle
    {X : Type} [TopologicalSpace X] [T2Space X]
    (E : C(Interval × Set.Icc (-1 : ℝ) 1,X))
    (K : Set X) (hK : IsClosed K) (c q : Interval)
    (V : Set Interval) (hV : IsOpen V) (hcV : c ∈ V)
    (hsole : ∀ t ∈ Set.Icc (0 : Interval) q,
      E (t,⟨0,by norm_num⟩) ∈ K → t = c)
    (η : ℝ) (hη : 0 < η)
    (hnear : ∀ t ∈ V, ∀ w : Set.Icc (-1 : ℝ) 1,
      0 < (w : ℝ) → (w : ℝ) < η → E (t,w) ∉ K) :
    ∃ ε : C(Interval,ℝ), ∃ hε : ∀ t, 0 ≤ ε t ∧ ε t < 1,
      (∀ t, t < q → 0 < ε t) ∧
      (∀ t, q ≤ t → ε t = 0) ∧
      ∀ t, t < q →
        E (t,⟨ε t,⟨by linarith [(hε t).1],(hε t).2.le⟩⟩) ∉ K := by
  let A : Set Interval := Set.Icc 0 q ∩ Vᶜ
  have hA : IsCompact A := isCompact_Icc.inter_right hV.isClosed_compl
  have hclear : ∀ t ∈ A, E (t,⟨0,by norm_num⟩) ∉ K := by
    intro t ht hbad
    exact ht.2 ((hsole t ht.1 hbad) ▸ hcV)
  obtain ⟨δ,hδ,hδclear⟩ := regional_strip_compact_parameter_clearance E A hA K hK hclear
  let d : ℝ := min δ (min η 1) / 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hdδ : d < δ := by dsimp [d]; linarith [min_le_left δ (min η 1)]
  have hdη : d < η := by
    dsimp [d]; linarith [min_le_right δ (min η 1),min_le_left η 1]
  have hd1 : d < 1 := by
    dsimp [d]; linarith [min_le_right δ (min η 1),min_le_right η 1]
  let ε : C(Interval,ℝ) := ⟨fun t => d * max ((q : ℝ)-(t : ℝ)) 0,by fun_prop⟩
  have hε : ∀ t, 0 ≤ ε t ∧ ε t < 1 := by
    intro t
    have hm0 : 0 ≤ max ((q : ℝ)-(t : ℝ)) 0 := le_max_right _ _
    have hm1 : max ((q : ℝ)-(t : ℝ)) 0 ≤ 1 :=
      max_le (by linarith [q.property.2,t.property.1]) (by norm_num)
    exact ⟨mul_nonneg hd.le hm0,
      (mul_le_mul_of_nonneg_left hm1 hd.le).trans_lt (by simpa using hd1)⟩
  have hεd : ∀ t, ε t ≤ d := by
    intro t
    exact (mul_le_mul_of_nonneg_left
      (max_le (by linarith [q.property.2,t.property.1]) (by norm_num)) hd.le).trans_eq
        (mul_one d)
  have hεpos : ∀ t, t < q → 0 < ε t := by
    intro t ht
    apply mul_pos hd
    exact lt_max_of_lt_left (sub_pos.mpr ht)
  refine ⟨ε,hε,hεpos,?_,?_⟩
  · intro t ht
    change d * max ((q : ℝ)-(t : ℝ)) 0 = 0
    rw [max_eq_right (sub_nonpos.mpr (show (q : ℝ) ≤ (t : ℝ) from ht)),mul_zero]
  · intro t ht
    let w : Set.Icc (-1 : ℝ) 1 := ⟨ε t,⟨by linarith [(hε t).1],(hε t).2.le⟩⟩
    by_cases htV : t ∈ V
    · exact hnear t htV w (hεpos t ht) ((hεd t).trans_lt hdη)
    · exact hδclear t ⟨⟨t.property.1,ht.le⟩,htV⟩ w
        (by change |ε t| < δ; rw [abs_of_nonneg (hε t).1]; exact (hεd t).trans_lt hdδ)

#print axioms regional_strip_compact_parameter_clearance
#print axioms regional_tapered_profile_avoids_prefix_obstacle
