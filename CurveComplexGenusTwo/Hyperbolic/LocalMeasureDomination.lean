import CurveComplexGenusTwo.Hyperbolic.NormalizedLocalArea

namespace CurveComplex.Hyperbolic

open MeasureTheory
open scoped ENNReal NNReal

theorem absolutelyContinuous_of_local_le
    {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] (ρ ν : Measure X)
    (h : ∀ x : X, ∃ (U : Set X) (c : ℝ≥0∞),
      IsOpen U ∧ x ∈ U ∧ ∀ s : Set X, s ⊆ U → ρ s ≤ c * ν s) :
    ρ ≪ ν := by
  classical
  choose U c hUo hUx hlocal using h
  have hcover : (Set.univ : Set X) ⊆ ⋃ x, U x := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hUx x⟩
  obtain ⟨r, hrcount, hrcovers⟩ :=
    isLindelof_univ.elim_countable_subcover U hUo hcover
  intro s hs
  have hpart (x : X) : ρ (s ∩ U x) = 0 := by
    have hν : ν (s ∩ U x) = 0 := measure_mono_null Set.inter_subset_left hs
    have hle := hlocal x (s ∩ U x) Set.inter_subset_right
    rw [hν, mul_zero] at hle
    exact nonpos_iff_eq_zero.mp hle
  have hunion : ρ (⋃ x ∈ r, s ∩ U x) = 0 :=
    (measure_biUnion_null_iff hrcount).2 fun x _ => hpart x
  have hsubset : s ⊆ ⋃ x ∈ r, s ∩ U x := by
    intro x hx
    obtain ⟨i, hir, hxi⟩ : ∃ i ∈ r, x ∈ U i := by
      simpa only [Set.mem_iUnion, exists_prop] using hrcovers (Set.mem_univ x)
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hir, ⟨hx, hxi⟩⟩⟩
  exact (measure_mono_null hsubset hunion)

theorem absolutelyContinuous_of_local_le_measurable
    {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] (ρ ν : Measure X)
    (h : ∀ x : X, ∃ (U : Set X) (c : ℝ≥0∞),
      IsOpen U ∧ x ∈ U ∧ ∀ s : Set X, MeasurableSet s → s ⊆ U → ρ s ≤ c * ν s) :
    ρ ≪ ν := by
  classical
  choose U c hUo hUx hlocal using h
  have hcover : (Set.univ : Set X) ⊆ ⋃ x, U x := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hUx x⟩
  obtain ⟨r, hrcount, hrcovers⟩ :=
    isLindelof_univ.elim_countable_subcover U hUo hcover
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hνs
  have hpart (x : X) : ρ (s ∩ U x) = 0 := by
    have hν : ν (s ∩ U x) = 0 := measure_mono_null Set.inter_subset_left hνs
    have hle := hlocal x (s ∩ U x) (hs.inter (hUo x).measurableSet)
      Set.inter_subset_right
    rw [hν, mul_zero] at hle
    exact nonpos_iff_eq_zero.mp hle
  have hunion : ρ (⋃ x ∈ r, s ∩ U x) = 0 :=
    (measure_biUnion_null_iff hrcount).2 fun x _ => hpart x
  have hsubset : s ⊆ ⋃ x ∈ r, s ∩ U x := by
    intro x hx
    obtain ⟨i, hir, hxi⟩ : ∃ i ∈ r, x ∈ U i := by
      simpa only [Set.mem_iUnion, exists_prop] using hrcovers (Set.mem_univ x)
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hir, ⟨hx, hxi⟩⟩⟩
  exact measure_mono_null hsubset hunion

theorem upperHalfPlane_normalizedHausdorff_absolutelyContinuous_coordinate :
    (μHE[2] : Measure UpperHalfPlane) ≪
      (volume : Measure ℂ).comap UpperHalfPlane.coe := by
  apply absolutelyContinuous_of_local_le
  intro z
  let r : ℝ := z.im / 2
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hrsmall : r < z.im := by dsimp [r]; linarith [z.im_pos]
  let U : Set UpperHalfPlane := {w | dist (w : ℂ) z < r}
  refine ⟨U, (localUpperNN z r hrsmall : ℝ≥0∞) ^ (2 : ℝ), ?_, ?_, ?_⟩
  · exact isOpen_lt (UpperHalfPlane.continuous_coe.dist continuous_const) continuous_const
  · dsimp [U]
    simpa using (show 0 < r by dsimp [r]; positivity)
  · intro s hs
    have hball : s ⊆ localEuclideanBall z r := by
      intro w hw
      have hwu := hs hw
      change dist (w : ℂ) (z : ℂ) < r at hwu
      exact le_of_lt hwu
    have hlocal := (upperHalfPlane_local_euclideanHausdorff_squeeze z hr hrsmall s hball).2
    have hle : (volume : Measure ℂ) (UpperHalfPlane.coe '' s) ≤
        ((volume : Measure ℂ).comap UpperHalfPlane.coe) s :=
      Measure.le_comap_apply UpperHalfPlane.coe (volume : Measure ℂ)
        UpperHalfPlane.coe_injective
        (fun t ht =>
          (UpperHalfPlane.measurableEmbedding_coe.measurableSet_image.mpr ht).nullMeasurableSet) s
    exact hlocal.trans (mul_le_mul_of_nonneg_left hle (by positivity))

theorem upperHalfPlane_coordinate_absolutelyContinuous_normalizedHausdorff :
    (volume : Measure ℂ).comap UpperHalfPlane.coe ≪
      (μHE[2] : Measure UpperHalfPlane) := by
  apply absolutelyContinuous_of_local_le_measurable
  intro z
  let r : ℝ := z.im / 2
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hrsmall : r < z.im := by dsimp [r]; linarith [z.im_pos]
  let U : Set UpperHalfPlane := {w | dist (w : ℂ) z < r}
  refine ⟨U, (localLowerInvNN z r hr hrsmall : ℝ≥0∞) ^ (2 : ℝ), ?_, ?_, ?_⟩
  · exact isOpen_lt (UpperHalfPlane.continuous_coe.dist continuous_const) continuous_const
  · dsimp [U]
    simpa using (show 0 < r by dsimp [r]; positivity)
  · intro s hs hsU
    have hball : s ⊆ localEuclideanBall z r := by
      intro w hw
      have hwu := hsU hw
      change dist (w : ℂ) (z : ℂ) < r at hwu
      exact le_of_lt hwu
    rw [Measure.comap_apply UpperHalfPlane.coe UpperHalfPlane.coe_injective
      (fun t ht => UpperHalfPlane.measurableEmbedding_coe.measurableSet_image.mpr ht)
      (volume : Measure ℂ) hs]
    exact (upperHalfPlane_local_euclideanHausdorff_squeeze z hr hrsmall s hball).1

noncomputable instance upperHalfPlane_normalizedHausdorff_locallyFinite :
    IsLocallyFiniteMeasure (μHE[2] : Measure UpperHalfPlane) := by
  refine ⟨fun z => ?_⟩
  let r : ℝ := z.im / 2
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hrsmall : r < z.im := by dsimp [r]; linarith [z.im_pos]
  let U : Set UpperHalfPlane := {w | dist (w : ℂ) z < r}
  have hUopen : IsOpen U :=
    isOpen_lt (UpperHalfPlane.continuous_coe.dist continuous_const) continuous_const
  have hzU : z ∈ U := by
    dsimp [U]
    simpa using (show 0 < r by dsimp [r]; positivity)
  have hball : U ⊆ localEuclideanBall z r := by
    intro w hw
    change dist (w : ℂ) (z : ℂ) < r at hw
    exact le_of_lt hw
  have himage : UpperHalfPlane.coe '' U ⊆ Metric.closedBall (z : ℂ) r := by
    rintro _ ⟨w, hw, rfl⟩
    change dist (w : ℂ) (z : ℂ) < r at hw
    exact le_of_lt hw
  have hfinite : (volume : Measure ℂ) (UpperHalfPlane.coe '' U) < ∞ :=
    (measure_mono himage).trans_lt measure_closedBall_lt_top
  have hbound := (upperHalfPlane_local_euclideanHausdorff_squeeze z hr hrsmall U hball).2
  refine ⟨U, hUopen.mem_nhds hzU, ?_⟩
  exact hbound.trans_lt (ENNReal.mul_lt_top (by finiteness) hfinite)

theorem upperHalfPlane_volume_absolutelyContinuous_coordinate :
    (volume : Measure UpperHalfPlane) ≪
      (volume : Measure ℂ).comap UpperHalfPlane.coe := by
  rw [UpperHalfPlane.volume_def]
  exact MeasureTheory.withDensity_absolutelyContinuous _ _

theorem upperHalfPlane_normalizedHausdorff_absolutelyContinuous_volume :
    (μHE[2] : Measure UpperHalfPlane) ≪
      (volume : Measure UpperHalfPlane) := by
  exact upperHalfPlane_normalizedHausdorff_absolutelyContinuous_coordinate.trans
    (by
      rw [UpperHalfPlane.volume_def]
      apply MeasureTheory.withDensity_absolutelyContinuous'
      · have hcont : Continuous (fun z : UpperHalfPlane =>
            (1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2) := by
          refine .pow (.div₀ continuous_const ?_ ?_) _
          · exact UpperHalfPlane.continuous_im.subtype_mk _
          · exact fun x => NNReal.ne_iff.mp x.im_ne_zero
        exact (measurable_coe_nnreal_ennreal.comp hcont.measurable).aemeasurable
      · filter_upwards [] with z
        have hy : 0 < (NNReal.mk z.im z.im_pos.le : ℝ≥0) := by
          exact NNReal.coe_pos.mp (by simpa using z.im_pos)
        have hf : 0 < (1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) := by positivity
        exact ne_of_gt (by exact_mod_cast (pow_pos hf 2)))

end CurveComplex.Hyperbolic
