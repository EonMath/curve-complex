import CurveComplexGenusTwo.Hyperbolic.LocalToGlobal

namespace CurveComplex.Hyperbolic

open MeasureTheory
open scoped NNReal ENNReal UpperHalfPlane Topology

private theorem inv_sq_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (1 / NNReal.mk b (le_trans ha.le hab) : ℝ≥0) ^ 2 ≤
      (1 / NNReal.mk a ha.le : ℝ≥0) ^ 2 := by
  have hmk : NNReal.mk a ha.le ≤ NNReal.mk b (le_trans ha.le hab) := by
    exact NNReal.coe_le_coe.mp (by simpa using hab)
  gcongr

private theorem height_band (z₀ w : UpperHalfPlane) {r : ℝ}
    (hr : 0 ≤ r) (hw : w ∈ localEuclideanBall z₀ r) :
    z₀.im - r ≤ w.im ∧ w.im ≤ z₀.im + r := by
  have hdist : dist (w : ℂ) (z₀ : ℂ) ≤ r := hw
  have him : |w.im - z₀.im| ≤ dist (w : ℂ) (z₀ : ℂ) := by
    simpa [Complex.sub_im, dist_eq_norm] using
      Complex.abs_im_le_norm ((w : ℂ) - (z₀ : ℂ))
  constructor <;> linarith [(abs_le.mp him).1, (abs_le.mp him).2]

private noncomputable def lowerDensityNN (z₀ : UpperHalfPlane) (r : ℝ)
    (hr : 0 ≤ r) : ℝ≥0 :=
  (1 / NNReal.mk (z₀.im + r) (by positivity) : ℝ≥0) ^ 2

private noncomputable def upperDensityNN (z₀ : UpperHalfPlane) (r : ℝ)
    (hrsmall : r < z₀.im) : ℝ≥0 :=
  (1 / NNReal.mk (z₀.im - r) (by linarith [hrsmall]) : ℝ≥0) ^ 2

private noncomputable def hyperbolicDensity (z : UpperHalfPlane) : ℝ≥0∞ :=
  ↑((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2)

private theorem density_band (z₀ w : UpperHalfPlane) {r : ℝ}
    (hr : 0 ≤ r) (hrsmall : r < z₀.im)
    (hw : w ∈ localEuclideanBall z₀ r) :
    (lowerDensityNN z₀ r hr : ℝ≥0∞) ≤ hyperbolicDensity w ∧
      hyperbolicDensity w ≤ (upperDensityNN z₀ r hrsmall : ℝ≥0∞) := by
  obtain ⟨hlo, hhi⟩ := height_band z₀ w hr hw
  constructor
  · change (lowerDensityNN z₀ r hr : ℝ≥0∞) ≤
      ↑((1 / NNReal.mk w.im w.im_pos.le : ℝ≥0) ^ 2)
    exact_mod_cast inv_sq_antitone w.im_pos hhi
  · change ↑((1 / NNReal.mk w.im w.im_pos.le : ℝ≥0) ^ 2) ≤
      (upperDensityNN z₀ r hrsmall : ℝ≥0∞)
    exact_mod_cast inv_sq_antitone (sub_pos.mpr hrsmall) hlo

private theorem volume_local_density_bounds (z₀ : UpperHalfPlane) {r : ℝ}
    (hr : 0 ≤ r) (hrsmall : r < z₀.im)
    (s : Set UpperHalfPlane) (hs : MeasurableSet s)
    (hsball : s ⊆ localEuclideanBall z₀ r) :
    (lowerDensityNN z₀ r hr : ℝ≥0∞) *
        (volume : Measure ℂ) (UpperHalfPlane.coe '' s) ≤
      (volume : Measure UpperHalfPlane) s ∧
    (volume : Measure UpperHalfPlane) s ≤
      (upperDensityNN z₀ r hrsmall : ℝ≥0∞) *
        (volume : Measure ℂ) (UpperHalfPlane.coe '' s) := by
  have hcoord : ((volume : Measure ℂ).comap UpperHalfPlane.coe) s =
      (volume : Measure ℂ) (UpperHalfPlane.coe '' s) :=
    Measure.comap_apply UpperHalfPlane.coe UpperHalfPlane.coe_injective
      (fun t ht => UpperHalfPlane.measurableEmbedding_coe.measurableSet_image.mpr ht)
      (volume : Measure ℂ) hs
  rw [UpperHalfPlane.volume_def]
  change _ ≤ ((volume : Measure ℂ).comap UpperHalfPlane.coe).withDensity
      hyperbolicDensity s ∧
    ((volume : Measure ℂ).comap UpperHalfPlane.coe).withDensity
      hyperbolicDensity s ≤ _
  rw [← hcoord]
  exact withDensity_set_bounds _ hyperbolicDensity hs _ _
    (fun w hw => (density_band z₀ w hr hrsmall (hsball hw)).1)
    (fun w hw => (density_band z₀ w hr hrsmall (hsball hw)).2)

private noncomputable def upperRatio (z₀ : UpperHalfPlane) (r : ℝ) : ℝ :=
  localUpperSlope z₀ r ^ 2 / (1 / (z₀.im + r)) ^ 2

private noncomputable def lowerRatio (z₀ : UpperHalfPlane) (r : ℝ) : ℝ :=
  (1 / (z₀.im - r)) ^ 2 * (localLowerSlope z₀ r)⁻¹ ^ 2

private theorem upperRatio_tendsto (z₀ : UpperHalfPlane) :
    Filter.Tendsto (upperRatio z₀) (nhds (0 : ℝ)) (nhds 1) := by
  have hcont : ContinuousAt (upperRatio z₀) 0 := by
    unfold upperRatio localUpperSlope
    fun_prop (disch := simp [ne_of_gt z₀.im_pos])
  convert hcont.tendsto using 1
  simp [upperRatio, localUpperSlope, ne_of_gt z₀.im_pos]

private theorem lowerRatio_tendsto (z₀ : UpperHalfPlane) :
    Filter.Tendsto (lowerRatio z₀) (nhds (0 : ℝ)) (nhds 1) := by
  have hcont : ContinuousAt (lowerRatio z₀) 0 := by
    unfold lowerRatio localLowerSlope
    fun_prop (disch := simp [ne_of_gt z₀.im_pos])
  convert hcont.tendsto using 1
  simp [lowerRatio, localLowerSlope, ne_of_gt z₀.im_pos]

private theorem exists_small_ratio_radius (z₀ : UpperHalfPlane) {c : ℝ} (hc : 1 < c) :
    ∃ r : ℝ, 0 < r ∧ r < z₀.im ∧
      upperRatio z₀ r < c ∧ lowerRatio z₀ r < c := by
  have hupper : ∀ᶠ r in 𝓝[>] (0 : ℝ), upperRatio z₀ r < c :=
    ((upperRatio_tendsto z₀).mono_left nhdsWithin_le_nhds).eventually
      (eventually_lt_nhds hc)
  have hlower : ∀ᶠ r in 𝓝[>] (0 : ℝ), lowerRatio z₀ r < c :=
    ((lowerRatio_tendsto z₀).mono_left nhdsWithin_le_nhds).eventually
      (eventually_lt_nhds hc)
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < z₀.im :=
    (eventually_lt_nhds z₀.im_pos).filter_mono nhdsWithin_le_nhds
  have hpositive : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
  exact (hpositive.and (hsmall.and (hupper.and hlower))).exists

private theorem upper_coefficient_le (z₀ : UpperHalfPlane) {r : ℝ} {c : ℝ≥0}
    (hr : 0 ≤ r) (hrsmall : r < z₀.im) (hc : 1 < (c : ℝ))
    (h : upperRatio z₀ r < c) :
    (localUpperNN z₀ r hrsmall : ℝ≥0∞) ^ (2 : ℝ) ≤
      (c : ℝ≥0∞) *
        (lowerDensityNN z₀ r hr : ℝ≥0∞) := by
  have hy : 0 < z₀.im + r := by linarith [z₀.im_pos]
  have hreal : localUpperSlope z₀ r ^ 2 ≤
      (c : ℝ) * (1 / (z₀.im + r)) ^ 2 := by
    have := le_of_lt h
    unfold upperRatio at this
    exact (div_le_iff₀ (pow_pos (one_div_pos.mpr hy) 2)).mp this
  have hnn : (localUpperNN z₀ r hrsmall : ℝ≥0) ^ 2 ≤
      c * lowerDensityNN z₀ r hr := by
    apply NNReal.coe_le_coe.mp
    change localUpperSlope z₀ r ^ 2 ≤
      (c : ℝ) * (1 / (z₀.im + r)) ^ 2
    exact hreal
  exact_mod_cast hnn

private theorem lower_coefficient_le (z₀ : UpperHalfPlane) {r : ℝ} {c : ℝ≥0}
    (hr : 0 ≤ r) (hrsmall : r < z₀.im) (hc : 1 < (c : ℝ))
    (h : lowerRatio z₀ r < c) :
    (upperDensityNN z₀ r hrsmall : ℝ≥0∞) *
      (localLowerInvNN z₀ r hr hrsmall : ℝ≥0∞) ^ (2 : ℝ) ≤
      (c : ℝ≥0∞) := by
  have hreal : (1 / (z₀.im - r)) ^ 2 *
      (localLowerSlope z₀ r)⁻¹ ^ 2 ≤ (c : ℝ) := by
    simpa only [lowerRatio] using le_of_lt h
  have hnn : upperDensityNN z₀ r hrsmall *
      (localLowerInvNN z₀ r hr hrsmall : ℝ≥0) ^ 2 ≤
      c := by
    apply NNReal.coe_le_coe.mp
    change (1 / (z₀.im - r)) ^ 2 *
      (localLowerSlope z₀ r)⁻¹ ^ 2 ≤ (c : ℝ)
    exact hreal
  exact_mod_cast hnn

private theorem local_fixed_factor (z₀ : UpperHalfPlane) {c : ℝ≥0}
    (hc : 1 < (c : ℝ)) :
    ∃ r : ℝ, 0 < r ∧ r < z₀.im ∧
      ∀ s : Set UpperHalfPlane, MeasurableSet s →
        s ⊆ localEuclideanBall z₀ r →
        (μHE[2] : Measure UpperHalfPlane) s ≤
            (c : ℝ≥0∞) * (volume : Measure UpperHalfPlane) s ∧
        (volume : Measure UpperHalfPlane) s ≤
            (c : ℝ≥0∞) * (μHE[2] : Measure UpperHalfPlane) s := by
  obtain ⟨r, hrpos, hrsmall, hupper, hlower⟩ :=
    exists_small_ratio_radius z₀ hc
  refine ⟨r, hrpos, hrsmall, ?_⟩
  intro s hs hsball
  have hmetric := upperHalfPlane_local_euclideanHausdorff_squeeze
    z₀ hrpos.le hrsmall s hsball
  have hvolume := volume_local_density_bounds z₀ hrpos.le hrsmall s hs hsball
  have huc := upper_coefficient_le z₀ hrpos.le hrsmall hc hupper
  have hlc := lower_coefficient_le z₀ hrpos.le hrsmall hc hlower
  constructor
  · calc
      (μHE[2] : Measure UpperHalfPlane) s ≤
          (localUpperNN z₀ r hrsmall : ℝ≥0∞) ^ (2 : ℝ) *
            (volume : Measure ℂ) (UpperHalfPlane.coe '' s) := hmetric.2
      _ ≤ ((c : ℝ≥0∞) * (lowerDensityNN z₀ r hrpos.le : ℝ≥0∞)) *
            (volume : Measure ℂ) (UpperHalfPlane.coe '' s) := by
          exact mul_le_mul_of_nonneg_right huc (by positivity)
      _ = (c : ℝ≥0∞) * ((lowerDensityNN z₀ r hrpos.le : ℝ≥0∞) *
            (volume : Measure ℂ) (UpperHalfPlane.coe '' s)) := by ac_rfl
      _ ≤ (c : ℝ≥0∞) * (volume : Measure UpperHalfPlane) s := by
          exact mul_le_mul_of_nonneg_left hvolume.1 (by positivity)
  · calc
      (volume : Measure UpperHalfPlane) s ≤
          (upperDensityNN z₀ r hrsmall : ℝ≥0∞) *
            (volume : Measure ℂ) (UpperHalfPlane.coe '' s) := hvolume.2
      _ ≤ (upperDensityNN z₀ r hrsmall : ℝ≥0∞) *
            ((localLowerInvNN z₀ r hrpos.le hrsmall : ℝ≥0∞) ^ (2 : ℝ) *
              (μHE[2] : Measure UpperHalfPlane) s) := by
          exact mul_le_mul_of_nonneg_left hmetric.1 (by positivity)
      _ = ((upperDensityNN z₀ r hrsmall : ℝ≥0∞) *
            (localLowerInvNN z₀ r hrpos.le hrsmall : ℝ≥0∞) ^ (2 : ℝ)) *
              (μHE[2] : Measure UpperHalfPlane) s := by ac_rfl
      _ ≤ (c : ℝ≥0∞) * (μHE[2] : Measure UpperHalfPlane) s := by
          exact mul_le_mul_of_nonneg_right hlc (by positivity)

private theorem global_fixed_factor (c : ℝ≥0) (hc : 1 < (c : ℝ)) :
    (μHE[2] : Measure UpperHalfPlane) ≤
        (c : ℝ≥0∞) • (volume : Measure UpperHalfPlane) ∧
    (volume : Measure UpperHalfPlane) ≤
        (c : ℝ≥0∞) • (μHE[2] : Measure UpperHalfPlane) := by
  constructor
  · apply measure_le_smul_of_local_measurable_le
    intro z
    obtain ⟨r, hrpos, hrsmall, h⟩ := local_fixed_factor z hc
    let U : Set UpperHalfPlane := {w | dist (w : ℂ) z < r}
    refine ⟨U, ?_, ?_, ?_⟩
    · exact isOpen_lt (UpperHalfPlane.continuous_coe.dist continuous_const)
        continuous_const
    · change dist (z : ℂ) (z : ℂ) < r
      simpa using hrpos
    · intro s hs hsU
      have hsball : s ⊆ localEuclideanBall z r := by
        intro w hw
        have hwu := hsU hw
        change dist (w : ℂ) (z : ℂ) < r at hwu
        exact le_of_lt hwu
      exact (h s hs hsball).1
  · apply measure_le_smul_of_local_measurable_le
    intro z
    obtain ⟨r, hrpos, hrsmall, h⟩ := local_fixed_factor z hc
    let U : Set UpperHalfPlane := {w | dist (w : ℂ) z < r}
    refine ⟨U, ?_, ?_, ?_⟩
    · exact isOpen_lt (UpperHalfPlane.continuous_coe.dist continuous_const)
        continuous_const
    · change dist (z : ℂ) (z : ℂ) < r
      simpa using hrpos
    · intro s hs hsU
      have hsball : s ⊆ localEuclideanBall z r := by
        intro w hw
        have hwu := hsU hw
        change dist (w : ℂ) (z : ℂ) < r at hwu
        exact le_of_lt hwu
      exact (h s hs hsball).2

private theorem measure_le_of_all_factors
    {X : Type*} [MeasurableSpace X] (ρ ν : Measure X)
    (h : ∀ c : ℝ≥0, (1 : ℝ) < c → ρ ≤ (c : ℝ≥0∞) • ν) :
    ρ ≤ ν := by
  refine Measure.le_iff.mpr fun s hs => ?_
  apply ENNReal.le_of_forall_lt_one_mul_le
  intro a ha
  by_cases ha0 : a = 0
  · simp [ha0]
  have hatop : a ≠ ∞ := ne_top_of_lt ha
  let b : ℝ≥0 := a.toNNReal
  have hb0 : b ≠ 0 := ne_of_gt (ENNReal.toNNReal_pos ha0 hatop)
  have hbcast : (b : ℝ≥0∞) = a := ENNReal.coe_toNNReal hatop
  have hb1 : b < (1 : ℝ≥0) := by
    exact_mod_cast (hbcast ▸ ha)
  have hc : (1 : ℝ) < (b⁻¹ : ℝ≥0) := by
    exact_mod_cast (one_lt_inv₀ (ENNReal.toNNReal_pos ha0 hatop)).mpr hb1
  have hmain : ρ s ≤ ((b⁻¹ : ℝ≥0) : ℝ≥0∞) * ν s := by
    simpa only [Measure.smul_apply, smul_eq_mul] using
      (Measure.le_iff.mp (h b⁻¹ hc) s hs)
  calc
    a * ρ s ≤ a * (((b⁻¹ : ℝ≥0) : ℝ≥0∞) * ν s) :=
      mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = ν s := by
      rw [ENNReal.coe_inv hb0, hbcast, ← mul_assoc,
        ENNReal.mul_inv_cancel ha0 hatop, one_mul]

theorem normalizedHausdorff_eq_upperHalfPlane_volume :
    (μHE[2] : Measure UpperHalfPlane) =
      (volume : Measure UpperHalfPlane) := by
  apply le_antisymm
  · exact measure_le_of_all_factors _ _ fun c hc => (global_fixed_factor c hc).1
  · exact measure_le_of_all_factors _ _ fun c hc => (global_fixed_factor c hc).2

noncomputable def upperHalfPlaneHausdorffScale : ℝ≥0 := by
  letI : (μH[2] : Measure (EuclideanSpace ℝ (Fin 2))).IsAddHaarMeasure := by
    simpa using (MeasureTheory.isAddHaarMeasure_hausdorffMeasure
      (E := EuclideanSpace ℝ (Fin 2)))
  exact Measure.addHaarScalarFactor
    (volume : Measure (EuclideanSpace ℝ (Fin 2)))
    (μH[2] : Measure (EuclideanSpace ℝ (Fin 2)))

theorem upperHalfPlaneHausdorffScale_pos : 0 < upperHalfPlaneHausdorffScale := by
  unfold upperHalfPlaneHausdorffScale
  letI : (μH[2] : Measure (EuclideanSpace ℝ (Fin 2))).IsAddHaarMeasure := by
    simpa using (MeasureTheory.isAddHaarMeasure_hausdorffMeasure
      (E := EuclideanSpace ℝ (Fin 2)))
  exact pos_iff_ne_zero.mpr
    (MeasureTheory.Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero 2)

theorem upperHalfPlane_rawHausdorff_eq_invScale_smul_volume :
    (μH[2] : Measure UpperHalfPlane) =
      upperHalfPlaneHausdorffScale⁻¹ • (volume : Measure UpperHalfPlane) := by
  calc
    (μH[2] : Measure UpperHalfPlane) =
        upperHalfPlaneHausdorffScale⁻¹ •
          (upperHalfPlaneHausdorffScale • (μH[2] : Measure UpperHalfPlane)) :=
      (inv_smul_smul₀ upperHalfPlaneHausdorffScale_pos.ne' _).symm
    _ = upperHalfPlaneHausdorffScale⁻¹ •
          (μHE[2] : Measure UpperHalfPlane) := by
      rw [Measure.euclideanHausdorffMeasure_def]
      rfl
    _ = upperHalfPlaneHausdorffScale⁻¹ •
          (volume : Measure UpperHalfPlane) := by
      rw [normalizedHausdorff_eq_upperHalfPlane_volume]

end CurveComplex.Hyperbolic
