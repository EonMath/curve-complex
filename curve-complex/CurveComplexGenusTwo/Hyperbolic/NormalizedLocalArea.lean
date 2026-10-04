import CurveComplexGenusTwo.Hyperbolic.LocalHausdorffComparison

namespace CurveComplex.Hyperbolic

open MeasureTheory
open scoped MeasureTheory ENNReal NNReal UpperHalfPlane

theorem LipschitzWith.euclideanHausdorffMeasure_image_le
    {X Y : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {f : X → Y} {K : ℝ≥0} (hf : LipschitzWith K f) (s : Set X) :
    (μHE[2] : Measure Y) (f '' s) ≤
      (K : ℝ≥0∞) ^ (2 : ℝ) * (μHE[2] : Measure X) s := by
  have h := hf.hausdorffMeasure_image_le (d := (2 : ℝ)) (by norm_num) s
  letI : (μH[2] : Measure (EuclideanSpace ℝ (Fin 2))).IsAddHaarMeasure := by
    simpa using (MeasureTheory.isAddHaarMeasure_hausdorffMeasure
      (E := EuclideanSpace ℝ (Fin 2)))
  unfold Measure.euclideanHausdorffMeasure
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  let c : ℝ≥0∞ := ↑(Measure.addHaarScalarFactor
    (volume : Measure (EuclideanSpace ℝ (Fin 2)))
    (μH[2] : Measure (EuclideanSpace ℝ (Fin 2))))
  calc
    c * μH[2] (f '' s) ≤ c * ((K : ℝ≥0∞)^(2 : ℝ) * μH[2] s) := by
      exact mul_le_mul_of_nonneg_left h (by positivity)
    _ = (K : ℝ≥0∞)^(2 : ℝ) * (c * μH[2] s) := by ac_rfl

theorem AntilipschitzWith.euclideanHausdorffMeasure_image_le
    {X Y : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {f : X → Y} {K : ℝ≥0} (hf : AntilipschitzWith K f) (s : Set X) :
    (μHE[2] : Measure X) s ≤
      (K : ℝ≥0∞) ^ (2 : ℝ) * (μHE[2] : Measure Y) (f '' s) := by
  have h := hf.le_hausdorffMeasure_image (d := (2 : ℝ)) (by norm_num) s
  letI : (μH[2] : Measure (EuclideanSpace ℝ (Fin 2))).IsAddHaarMeasure := by
    simpa using (MeasureTheory.isAddHaarMeasure_hausdorffMeasure
      (E := EuclideanSpace ℝ (Fin 2)))
  unfold Measure.euclideanHausdorffMeasure
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  let c : ℝ≥0∞ := ↑(Measure.addHaarScalarFactor
    (volume : Measure (EuclideanSpace ℝ (Fin 2)))
    (μH[2] : Measure (EuclideanSpace ℝ (Fin 2))))
  calc
    c * μH[2] s ≤ c * ((K : ℝ≥0∞)^(2 : ℝ) * μH[2] (f '' s)) := by
      exact mul_le_mul_of_nonneg_left h (by positivity)
    _ = (K : ℝ≥0∞)^(2 : ℝ) * (c * μH[2] (f '' s)) := by ac_rfl

theorem localEuclideanBall_euclideanHausdorff_squeeze
    (z₀ : UpperHalfPlane) {r : ℝ} (hr : 0 ≤ r)
    (hrsmall : r < z₀.im)
    (s : Set (localEuclideanBall z₀ r)) :
    (μHE[2] : Measure ℂ)
        ((fun z : localEuclideanBall z₀ r => (z.1 : ℂ)) '' s) ≤
      (localLowerInvNN z₀ r hr hrsmall : ℝ≥0∞) ^ (2 : ℝ) *
        (μHE[2] : Measure (localEuclideanBall z₀ r)) s ∧
    (μHE[2] : Measure (localEuclideanBall z₀ r)) s ≤
      (localUpperNN z₀ r hrsmall : ℝ≥0∞) ^ (2 : ℝ) *
        (μHE[2] : Measure ℂ)
          ((fun z : localEuclideanBall z₀ r => (z.1 : ℂ)) '' s) := by
  constructor
  · exact LipschitzWith.euclideanHausdorffMeasure_image_le
      (localEuclideanBall_coe_lipschitz z₀ hr hrsmall) s
  · exact AntilipschitzWith.euclideanHausdorffMeasure_image_le
      (localEuclideanBall_coe_antilipschitz z₀ hr hrsmall) s

theorem upperHalfPlane_local_euclideanHausdorff_squeeze
    (z₀ : UpperHalfPlane) {r : ℝ} (hr : 0 ≤ r)
    (hrsmall : r < z₀.im)
    (s : Set UpperHalfPlane) (hs : s ⊆ localEuclideanBall z₀ r) :
    (volume : Measure ℂ) (UpperHalfPlane.coe '' s) ≤
      (localLowerInvNN z₀ r hr hrsmall : ℝ≥0∞) ^ (2 : ℝ) *
        (μHE[2] : Measure UpperHalfPlane) s ∧
    (μHE[2] : Measure UpperHalfPlane) s ≤
      (localUpperNN z₀ r hrsmall : ℝ≥0∞) ^ (2 : ℝ) *
        (volume : Measure ℂ) (UpperHalfPlane.coe '' s) := by
  let t : Set (localEuclideanBall z₀ r) := {z | z.1 ∈ s}
  have himage : ((↑) : localEuclideanBall z₀ r → UpperHalfPlane) '' t = s := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hz
      exact ⟨⟨z, hs hz⟩, hz, rfl⟩
  have hcomplex : (fun z : localEuclideanBall z₀ r => (z.1 : ℂ)) '' t =
      UpperHalfPlane.coe '' s := by
    rw [← himage, Set.image_image]
  have hμ : (μHE[2] : Measure UpperHalfPlane) s =
      (μHE[2] : Measure (localEuclideanBall z₀ r)) t := by
    rw [← himage]
    simp only [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply]
    rw [isometry_subtype_coe.hausdorffMeasure_image (by norm_num) t]
  simpa only [hcomplex, hμ, ← complex_volume_eq_normalized_hausdorff] using
    localEuclideanBall_euclideanHausdorff_squeeze z₀ hr hrsmall t

end CurveComplex.Hyperbolic
