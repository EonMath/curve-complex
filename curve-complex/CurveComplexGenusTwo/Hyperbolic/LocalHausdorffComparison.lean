import CurveComplexGenusTwo.Hyperbolic.LocalMetricComparison
import CurveComplexGenusTwo.Hyperbolic.MetricMeasureBridge

namespace CurveComplex.Hyperbolic

open MeasureTheory
open scoped MeasureTheory NNReal ENNReal UpperHalfPlane

def localEuclideanBall (z₀ : UpperHalfPlane) (r : ℝ) : Set UpperHalfPlane :=
  {z | dist (z : ℂ) z₀ ≤ r}

noncomputable def localUpperNN (z₀ : UpperHalfPlane) (r : ℝ)
    (hr : r < z₀.im) : ℝ≥0 :=
  ⟨localUpperSlope z₀ r, by unfold localUpperSlope; positivity⟩

noncomputable def localLowerInvNN (z₀ : UpperHalfPlane) (r : ℝ)
    (hr : 0 ≤ r) (hrsmall : r < z₀.im) : ℝ≥0 :=
  ⟨(localLowerSlope z₀ r)⁻¹, by
    have hpos : 0 < localLowerSlope z₀ r := by
      unfold localLowerSlope
      positivity
    positivity⟩

theorem localEuclideanBall_coe_lipschitz
    (z₀ : UpperHalfPlane) {r : ℝ} (hr : 0 ≤ r)
    (hrsmall : r < z₀.im) :
    LipschitzWith (localLowerInvNN z₀ r hr hrsmall)
      (fun z : localEuclideanBall z₀ r => (z.1 : ℂ)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have h := (upperHalfPlane_local_dist_squeeze_slopes z₀ z.1 w.1
    hr hrsmall z.2 w.2).1
  change dist (z.1 : ℂ) (w.1 : ℂ) ≤
    (localLowerSlope z₀ r)⁻¹ * dist z.1 w.1
  have hpos : 0 < localLowerSlope z₀ r := by
    unfold localLowerSlope
    positivity
  rw [← div_eq_inv_mul]
  exact (le_div_iff₀ hpos).2 (by simpa [mul_comm] using h)

theorem localEuclideanBall_coe_antilipschitz
    (z₀ : UpperHalfPlane) {r : ℝ} (hr : 0 ≤ r)
    (hrsmall : r < z₀.im) :
    AntilipschitzWith (localUpperNN z₀ r hrsmall)
      (fun z : localEuclideanBall z₀ r => (z.1 : ℂ)) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro z w
  have h := (upperHalfPlane_local_dist_squeeze_slopes z₀ z.1 w.1
    hr hrsmall z.2 w.2).2
  exact h

theorem localEuclideanBall_hausdorff_squeeze
    (z₀ : UpperHalfPlane) {r : ℝ} (hr : 0 ≤ r)
    (hrsmall : r < z₀.im)
    (s : Set (localEuclideanBall z₀ r)) :
    (μH[2] : Measure ℂ)
        ((fun z : localEuclideanBall z₀ r => (z.1 : ℂ)) '' s) ≤
      (localLowerInvNN z₀ r hr hrsmall : ℝ≥0∞) ^ (2 : ℝ) *
        (μH[2] : Measure (localEuclideanBall z₀ r)) s ∧
    (μH[2] : Measure (localEuclideanBall z₀ r)) s ≤
      (localUpperNN z₀ r hrsmall : ℝ≥0∞) ^ (2 : ℝ) *
        (μH[2] : Measure ℂ)
          ((fun z : localEuclideanBall z₀ r => (z.1 : ℂ)) '' s) := by
  constructor
  · exact (localEuclideanBall_coe_lipschitz z₀ hr hrsmall)
      |>.hausdorffMeasure_image_le (by norm_num) s
  · exact (localEuclideanBall_coe_antilipschitz z₀ hr hrsmall)
      |>.le_hausdorffMeasure_image (by norm_num) s

theorem upperHalfPlane_local_hausdorff_squeeze
    (z₀ : UpperHalfPlane) {r : ℝ} (hr : 0 ≤ r)
    (hrsmall : r < z₀.im)
    (s : Set UpperHalfPlane) (hs : s ⊆ localEuclideanBall z₀ r) :
    (μH[2] : Measure ℂ) (UpperHalfPlane.coe '' s) ≤
      (localLowerInvNN z₀ r hr hrsmall : ℝ≥0∞) ^ (2 : ℝ) *
        (μH[2] : Measure UpperHalfPlane) s ∧
    (μH[2] : Measure UpperHalfPlane) s ≤
      (localUpperNN z₀ r hrsmall : ℝ≥0∞) ^ (2 : ℝ) *
        (μH[2] : Measure ℂ) (UpperHalfPlane.coe '' s) := by
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
  have hμ : (μH[2] : Measure UpperHalfPlane) s =
      (μH[2] : Measure (localEuclideanBall z₀ r)) t := by
    rw [← himage]
    exact isometry_subtype_coe.hausdorffMeasure_image (by norm_num) t
  simpa [hcomplex, hμ] using
    localEuclideanBall_hausdorff_squeeze z₀ hr hrsmall t

theorem upperHalfPlane_local_hausdorff_squeeze_volume
    (z₀ : UpperHalfPlane) {r : ℝ} (hr : 0 ≤ r)
    (hrsmall : r < z₀.im)
    (s : Set UpperHalfPlane) (hs : s ⊆ localEuclideanBall z₀ r) :
    (volume : Measure ℂ) (UpperHalfPlane.coe '' s) ≤
      (complexHausdorffScale : ℝ≥0∞) *
        (localLowerInvNN z₀ r hr hrsmall : ℝ≥0∞) ^ (2 : ℝ) *
        (μH[2] : Measure UpperHalfPlane) s ∧
    (μH[2] : Measure UpperHalfPlane) s ≤
      (localUpperNN z₀ r hrsmall : ℝ≥0∞) ^ (2 : ℝ) *
        ((complexHausdorffScale⁻¹ : ℝ≥0) : ℝ≥0∞) *
          (volume : Measure ℂ) (UpperHalfPlane.coe '' s) := by
  have h := upperHalfPlane_local_hausdorff_squeeze z₀ hr hrsmall s hs
  constructor
  · rw [complex_volume_eq_scale_smul_hausdorff, Measure.smul_apply,
      ENNReal.smul_def]
    have hmul := mul_le_mul_of_nonneg_left h.1 (by positivity :
      0 ≤ (complexHausdorffScale : ℝ≥0∞))
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  · rw [complex_hausdorff_eq_inv_scale_smul_volume, Measure.smul_apply,
      ENNReal.smul_def] at h
    simpa [mul_assoc] using h.2

end CurveComplex.Hyperbolic
