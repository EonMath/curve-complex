import Mathlib
import Mathlib.Geometry.Euclidean.Volume.Measure

namespace CurveComplex.Hyperbolic

open MeasureTheory Measure
open scoped MeasureTheory UpperHalfPlane NNReal ENNReal

/-- In the Euclidean complex plane Mathlib relates Lebesgue volume to the
normalized Euclidean Hausdorff measure `μHE[2]`. -/
theorem complex_volume_eq_normalized_hausdorff :
    (volume : Measure ℂ) = (μHE[2] : Measure ℂ) := by
  simpa [Complex.finrank_real_complex] using
    (InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := ℂ)).symm

noncomputable def complexHausdorffScale : ℝ≥0 := by
  letI : (μH[2] : Measure ℂ).IsAddHaarMeasure := by
    simpa [Complex.finrank_real_complex] using
      (inferInstance : (μH[Module.finrank ℝ ℂ] : Measure ℂ).IsAddHaarMeasure)
  exact addHaarScalarFactor (volume : Measure ℂ) (μH[2] : Measure ℂ)

theorem complex_volume_eq_scale_smul_hausdorff :
    (volume : Measure ℂ) =
      complexHausdorffScale • (μH[2] : Measure ℂ) := by
  unfold complexHausdorffScale
  letI : (μH[2] : Measure ℂ).IsAddHaarMeasure := by
    simpa [Complex.finrank_real_complex] using
      (inferInstance : (μH[Module.finrank ℝ ℂ] : Measure ℂ).IsAddHaarMeasure)
  exact isAddLeftInvariant_eq_smul (volume : Measure ℂ) (μH[2] : Measure ℂ)

theorem complexHausdorffScale_pos : 0 < complexHausdorffScale := by
  unfold complexHausdorffScale
  letI : (μH[2] : Measure ℂ).IsAddHaarMeasure := by
    simpa [Complex.finrank_real_complex] using
      (inferInstance : (μH[Module.finrank ℝ ℂ] : Measure ℂ).IsAddHaarMeasure)
  exact addHaarScalarFactor_pos_of_isAddHaarMeasure
    (volume : Measure ℂ) (μH[2] : Measure ℂ)

theorem complex_hausdorff_eq_inv_scale_smul_volume :
    (μH[2] : Measure ℂ) = complexHausdorffScale⁻¹ • (volume : Measure ℂ) := by
  calc
    (μH[2] : Measure ℂ) = complexHausdorffScale⁻¹ •
        (complexHausdorffScale • (μH[2] : Measure ℂ)) :=
      (inv_smul_smul₀ complexHausdorffScale_pos.ne' _).symm
    _ = complexHausdorffScale⁻¹ • (volume : Measure ℂ) := by
      rw [← complex_volume_eq_scale_smul_hausdorff]

/-- On a horoball tail, hyperbolic distance is bounded by Euclidean distance
with the expected inverse-height factor. -/
theorem upperHalfPlane_dist_le_euclidean_div_height
    {c : ℝ} (hc : 0 < c) (z w : UpperHalfPlane)
    (hz : c ≤ z.im) (hw : c ≤ w.im) :
    dist z w ≤ dist (z : ℂ) w / c := by
  have hsqrt : c ≤ Real.sqrt (z.im * w.im) := by
    apply Real.le_sqrt hc.le (mul_nonneg (le_trans hc.le hz) (le_trans hc.le hw)) |>.2
    nlinarith [mul_nonneg (sub_nonneg.mpr hz) (sub_nonneg.mpr hw)]
  calc
    dist z w ≤ dist (z : ℂ) w / Real.sqrt (z.im * w.im) :=
      UpperHalfPlane.dist_le_dist_coe_div_sqrt z w
    _ ≤ dist (z : ℂ) w / c := by gcongr

def upperHeightTail (c : ℝ) : Set UpperHalfPlane := {z | c ≤ z.im}

noncomputable def reciprocalHeight (c : ℝ) (hc : 0 < c) : ℝ≥0 :=
  ⟨1 / c, by positivity⟩

/-- The coordinate embedding is globally antilipschitz on every fixed-height
tail, so it controls the hyperbolic Hausdorff measure there. -/
theorem upperHeightTail_coe_antilipschitz {c : ℝ} (hc : 0 < c) :
    AntilipschitzWith (reciprocalHeight c hc)
      (fun z : upperHeightTail c => (z.1 : ℂ)) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro z w
  change dist z.1 w.1 ≤
    (reciprocalHeight c hc : ℝ) * dist (z.1 : ℂ) (w.1 : ℂ)
  change dist z.1 w.1 ≤ (1 / c) * dist (z.1 : ℂ) (w.1 : ℂ)
  simpa [div_eq_mul_inv, mul_comm] using
    upperHalfPlane_dist_le_euclidean_div_height hc z.1 w.1 z.2 w.2

theorem upperHeightTail_hausdorff_le_euclidean {c : ℝ} (hc : 0 < c)
    (s : Set (upperHeightTail c)) :
    (μH[2] : Measure (upperHeightTail c)) s ≤
      (reciprocalHeight c hc : ℝ≥0∞) ^ (2 : ℝ) *
        (μH[2] : Measure ℂ) ((fun z : upperHeightTail c => (z.1 : ℂ)) '' s) := by
  exact (upperHeightTail_coe_antilipschitz hc).le_hausdorffMeasure_image
    (by norm_num) s

theorem upperHalfPlane_hausdorff_tail_le_euclidean {c : ℝ} (hc : 0 < c)
    (s : Set UpperHalfPlane) (hs : s ⊆ upperHeightTail c) :
    (μH[2] : Measure UpperHalfPlane) s ≤
      (reciprocalHeight c hc : ℝ≥0∞) ^ (2 : ℝ) *
        (μH[2] : Measure ℂ) (UpperHalfPlane.coe '' s) := by
  let t : Set (upperHeightTail c) := {z | (z.1 : UpperHalfPlane) ∈ s}
  have himage : ((↑) : upperHeightTail c → UpperHalfPlane) '' t = s := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hz
      exact ⟨⟨z, hs hz⟩, hz, rfl⟩
  have hcomplex : (fun z : upperHeightTail c => (z.1 : ℂ)) '' t =
      UpperHalfPlane.coe '' s := by
    rw [← himage, Set.image_image]
  calc
    (μH[2] : Measure UpperHalfPlane) s =
        (μH[2] : Measure (upperHeightTail c)) t := by
          rw [← himage]
          exact isometry_subtype_coe.hausdorffMeasure_image (by norm_num) t
    _ ≤ (reciprocalHeight c hc : ℝ≥0∞) ^ (2 : ℝ) *
        (μH[2] : Measure ℂ) ((fun z : upperHeightTail c => (z.1 : ℂ)) '' t) :=
      upperHeightTail_hausdorff_le_euclidean hc t
    _ = _ := by rw [hcomplex]

/-- A concrete one-sided coordinate-volume/Hausdorff bridge on a cusp tail.
The scalar is Mathlib's Euclidean Hausdorff normalization, which the library
does not identify numerically. -/
theorem upperHalfPlane_hausdorff_tail_le_coordinate_volume
    {c : ℝ} (hc : 0 < c) (s : Set UpperHalfPlane)
    (hs : s ⊆ upperHeightTail c) :
    (μH[2] : Measure UpperHalfPlane) s ≤
      (reciprocalHeight c hc : ℝ≥0∞) ^ (2 : ℝ) *
        ((complexHausdorffScale⁻¹ : ℝ≥0) : ℝ≥0∞) *
          (volume : Measure ℂ) (UpperHalfPlane.coe '' s) := by
  have h := upperHalfPlane_hausdorff_tail_le_euclidean hc s hs
  rw [complex_hausdorff_eq_inv_scale_smul_volume, Measure.smul_apply,
    ENNReal.smul_def] at h
  simpa [mul_assoc] using h

theorem complex_hausdorff_finite_of_isCompact (s : Set ℂ) (hs : IsCompact s) :
    (μH[2] : Measure ℂ) s ≠ ⊤ := by
  letI : (μH[2] : Measure ℂ).IsAddHaarMeasure := by
    simpa [Complex.finrank_real_complex] using
      (inferInstance : (μH[Module.finrank ℝ ℂ] : Measure ℂ).IsAddHaarMeasure)
  exact (IsFiniteMeasureOnCompacts.lt_top_of_isCompact hs).ne

/-- Finite hyperbolic Hausdorff area on any fixed-height region whose
Euclidean coordinate image is compact. -/
theorem upperHalfPlane_hausdorff_tail_finite_of_compact_coordinate
    {c : ℝ} (hc : 0 < c) (s : Set UpperHalfPlane)
    (hs : s ⊆ upperHeightTail c)
    (hcompact : IsCompact (UpperHalfPlane.coe '' s)) :
    (μH[2] : Measure UpperHalfPlane) s ≠ ⊤ := by
  have hbound := upperHalfPlane_hausdorff_tail_le_euclidean hc s hs
  have hfinite := complex_hausdorff_finite_of_isCompact _ hcompact
  exact (hbound.trans_lt (ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.coe_ne_top)
    hfinite.lt_top)).ne

end CurveComplex.Hyperbolic
