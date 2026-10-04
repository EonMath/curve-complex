import CurveComplexGenusTwo.Topology.FareyJoinContraction

set_option maxHeartbeats 1000000

namespace CurveComplexGenusTwo.Topology

open CurveComplex Set unitInterval

private theorem normalized_chart_continuousOn
    (face : Finset (Sum FareySlope FareySlope))
    (hface : face ∈ fareyJoinComplex.faces)
    (base : RealizationPoint fareyFlagComplex) :
    ContinuousOn
      (fun z : I × FiniteSimplex face =>
        if hm : 0 < fareyJoinLeftMass
            (faceInclusion fareyJoinComplex face hface z.2) then
          fareyJoinNormalizeLeft
            (faceInclusion fareyJoinComplex face hface z.2) hm
        else base)
      {z | 0 < fareyJoinLeftMass
        (faceInclusion fareyJoinComplex face hface z.2)} := by
  let s : Set (I × FiniteSimplex face) :=
    {z | 0 < fareyJoinLeftMass
      (faceInclusion fareyJoinComplex face hface z.2)}
  have hx : Continuous (fun z : s =>
      faceInclusion fareyJoinComplex face hface z.1.2) :=
    (continuous_faceInclusion fareyJoinComplex face hface).comp
      (continuous_snd.comp continuous_subtype_val)
  have hbound : ∀ z : s,
      supportFinset fareyJoinComplex
        (faceInclusion fareyJoinComplex face hface z.1.2) ⊆ face := by
    intro z u hu
    by_contra hnot
    exact ((mem_supportFinset_iff fareyJoinComplex _ u).1 hu)
      (faceInclusion_weight_of_not_mem fareyJoinComplex face hface z.1.2 u hnot)
  have hm : ∀ z : s, 0 < fareyJoinLeftMass
      (faceInclusion fareyJoinComplex face hface z.1.2) :=
    fun z => z.2
  have hn := fareyJoinNormalizeLeft_continuous_of_faceBound
    (fun z : s => faceInclusion fareyJoinComplex face hface z.1.2)
    face hx hbound hm
  rw [continuousOn_iff_continuous_domRestrict]
  convert hn using 1
  funext z
  dsimp only [Set.domRestrict]
  split_ifs with h
  · rfl
  · exact (h z.2).elim

private theorem factor_homotopy_face_support_bound
    (base : RealizationPoint fareyFlagComplex)
    (H : ContinuousMap.Homotopy
      (ContinuousMap.id (RealizationPoint fareyFlagComplex))
      (ContinuousMap.const (RealizationPoint fareyFlagComplex) base))
    (F : Finset FareySlope) :
    ∃ G : Finset FareySlope,
      ∀ (t : I) (p : RealizationPoint fareyFlagComplex),
        supportFinset fareyFlagComplex p ⊆ F →
        supportFinset fareyFlagComplex (H (t, p)) ⊆ G := by
  letI : CompactSpace (finiteSupportLocus fareyFlagComplex F) :=
    (isCompact_iff_compactSpace).mp
      (isCompact_finiteSupportLocus fareyFlagComplex F)
  let h : I × finiteSupportLocus fareyFlagComplex F →
      RealizationPoint fareyFlagComplex := fun z => H (z.1, z.2.1)
  have hc : Continuous h :=
    H.continuous.comp (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd))
  obtain ⟨G, hG⟩ := compact_realization_has_finite_support
    fareyFlagComplex (Set.range h) (isCompact_range hc)
  refine ⟨G, ?_⟩
  intro t p hp
  exact hG (H (t, p)) ⟨(t, ⟨p, hp⟩), rfl⟩

/-- The left-factor replacement homotopy is jointly continuous for the actual
weak topology on the join realization. -/
theorem fareyJoinReplaceLeft_continuous
    (base : RealizationPoint fareyFlagComplex)
    (H : ContinuousMap.Homotopy
      (ContinuousMap.id (RealizationPoint fareyFlagComplex))
      (ContinuousMap.const (RealizationPoint fareyFlagComplex) base)) :
    Continuous (fun z : I × RealizationPoint fareyJoinComplex =>
      fareyJoinReplaceLeft base H z.1 z.2) := by
  classical
  apply (continuous_iff_continuous_on_face_time_charts fareyJoinComplex _).2
  intro face hface
  let x : I × FiniteSimplex face → RealizationPoint fareyJoinComplex :=
    fun z => faceInclusion fareyJoinComplex face hface z.2
  let m : I × FiniteSimplex face → ℝ := fun z => fareyJoinLeftMass (x z)
  let n : I × FiniteSimplex face → RealizationPoint fareyFlagComplex :=
    fun z => if hm : 0 < m z then fareyJoinNormalizeLeft (x z) hm else base
  let q : I × FiniteSimplex face → RealizationPoint fareyFlagComplex :=
    fun z => H (z.1, n z)
  have hx : Continuous x :=
    (continuous_faceInclusion fareyJoinComplex face hface).comp continuous_snd
  have hm : Continuous m := fareyJoinLeftMass_continuous.comp hx
  have hm0 : ∀ z, 0 ≤ m z := fun z => fareyJoinLeftMass_nonneg (x z)
  have hn : ContinuousOn n {z | m z ≠ 0} := by
    have hpos : {z : I × FiniteSimplex face | m z ≠ 0} =
        {z | 0 < m z} := by
      ext z
      exact ne_iff_lt_or_gt.trans (by
        constructor
        · rintro (hneg | hpos)
          · exact False.elim ((not_lt_of_ge (hm0 z)) hneg)
          · exact hpos
        · exact Or.inr)
    rw [hpos]
    exact normalized_chart_continuousOn face hface base
  have hq : ContinuousOn q {z | m z ≠ 0} :=
    H.continuous.continuousOn.comp'
      (continuous_fst.continuousOn.prodMk hn)
      (fun z hz => Set.mem_univ _)
  obtain ⟨G, hG⟩ := factor_homotopy_face_support_bound
    base H (fareyJoinLeft face)
  let B : Finset (Sum FareySlope FareySlope) := G.image Sum.inl ∪ face
  change Continuous (fun p : I × FiniteSimplex face =>
    fareyJoinReplaceLeft base H p.1 (x p))
  apply continuous_of_finite_support_and_coordinates fareyJoinComplex B
  · intro z s hs
    cases s with
    | inl a =>
        by_cases hp : 0 < m z
        · have hnface : supportFinset fareyFlagComplex (n z) ⊆
              fareyJoinLeft face := by
            simp only [n, dif_pos hp]
            apply (fareyJoinNormalizeLeft_support_subset (x z) hp).trans
            intro u hu
            exact (mem_fareyJoinLeft_iff face u).2
              (faceInclusion_support_subset fareyJoinComplex face hface z.2
                ((mem_supportFinset_iff fareyJoinComplex (x z) (.inl u)).1
                  ((mem_fareyJoinLeft_iff _ u).1 hu)))
          have hqG := hG z.1 (n z) hnface
          have haq : a ∈ supportFinset fareyFlagComplex (q z) := by
            by_contra hna
            have hzero : (q z).weight a = 0 := by
              by_contra hnon
              exact hna ((mem_supportFinset_iff fareyFlagComplex _ a).2 hnon)
            exact ((mem_supportFinset_iff fareyJoinComplex _ (.inl a)).1 hs)
              (by rw [fareyJoinReplaceLeft_weight_inl_of_pos base H z.1 (x z) hp a]
                  simpa [q, n, hp] using (mul_eq_zero.mpr (Or.inr hzero)))
          exact Finset.mem_union_left _ (Finset.mem_image.mpr
            ⟨a, hqG haq, rfl⟩)
        · have hzero : m z = 0 := le_antisymm (le_of_not_gt hp) (hm0 z)
          have hweight := fareyJoinLeftWeight_zero_of_mass_zero (x z) hzero a
          exact False.elim (((mem_supportFinset_iff fareyJoinComplex _ (.inl a)).1 hs)
            (by simpa [fareyJoinReplaceLeft, m, hp] using hweight))
    | inr b =>
        by_cases hb : Sum.inr b ∈ face
        · exact Finset.mem_union_right _ hb
        · have hzero := faceInclusion_weight_of_not_mem
            fareyJoinComplex face hface z.2 (.inr b) hb
          exact False.elim (((mem_supportFinset_iff fareyJoinComplex _ (.inr b)).1 hs)
            (by by_cases hp : 0 < m z
                · simpa [x] using
                    (fareyJoinReplaceLeft_weight_inr_of_pos base H z.1 (x z) hp b).trans hzero
                · simpa [fareyJoinReplaceLeft, m, hp, x] using hzero))
  · intro s
    cases s.1 with
    | inl a =>
        have heq : (fun z : I × FiniteSimplex face =>
            (fareyJoinReplaceLeft base H z.1 (x z)).weight (.inl a)) =
            fun z => m z * (q z).weight a := by
          funext z
          by_cases hp : 0 < m z
          · simpa [q, n, m, hp] using
              fareyJoinReplaceLeft_weight_inl_of_pos base H z.1 (x z) hp a
          · have hzero : m z = 0 := le_antisymm (le_of_not_gt hp) (hm0 z)
            simp [fareyJoinReplaceLeft, m, hp, hzero,
              fareyJoinLeftWeight_zero_of_mass_zero (x z) hzero a]
        rw [heq]
        exact weighted_farey_coordinate_continuous m q hm hm0 hq a
    | inr b =>
        have heq : (fun z : I × FiniteSimplex face =>
            (fareyJoinReplaceLeft base H z.1 (x z)).weight (.inr b)) =
            fun z => (x z).weight (.inr b) := by
          funext z
          by_cases hp : 0 < m z
          · exact fareyJoinReplaceLeft_weight_inr_of_pos base H z.1 (x z) hp b
          · simp [fareyJoinReplaceLeft, m, hp]
        rw [heq]
        exact (continuous_weight fareyJoinComplex (.inr b)).comp hx

end CurveComplexGenusTwo.Topology
