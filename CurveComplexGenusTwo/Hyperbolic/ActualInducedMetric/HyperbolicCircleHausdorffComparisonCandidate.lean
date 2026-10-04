import CurveComplexGenusTwo.Hyperbolic.LocalHausdorffComparison

namespace CurveComplex.Hyperbolic
open Set MeasureTheory
open scoped NNReal ENNReal UpperHalfPlane

theorem upperHalfPlane_local_hausdorff_length_squeeze
    (z₀ : UpperHalfPlane) {r : ℝ} (hr : 0 ≤ r) (hrsmall : r < z₀.im)
    (s : Set UpperHalfPlane) (hs : s ⊆ localEuclideanBall z₀ r) :
    (Measure.hausdorffMeasure 1 : Measure ℂ) (UpperHalfPlane.coe '' s) ≤
      (localLowerInvNN z₀ r hr hrsmall : ℝ≥0∞) *
        (Measure.hausdorffMeasure 1 : Measure UpperHalfPlane) s ∧
    (Measure.hausdorffMeasure 1 : Measure UpperHalfPlane) s ≤
      (localUpperNN z₀ r hrsmall : ℝ≥0∞) *
        (Measure.hausdorffMeasure 1 : Measure ℂ) (UpperHalfPlane.coe '' s) := by
  let t : Set (localEuclideanBall z₀ r) := {z | z.val ∈ s}
  have himage : Subtype.val '' t = s := by
    ext z; constructor
    · rintro ⟨w, hw, rfl⟩; exact hw
    · intro hz; exact ⟨⟨z, hs hz⟩, hz, rfl⟩
  have hcomplex : (fun z : localEuclideanBall z₀ r => (z.val : ℂ)) '' t =
      UpperHalfPlane.coe '' s := by
    rw [← himage, image_image]
  have hμ : (Measure.hausdorffMeasure 1 : Measure UpperHalfPlane) s =
      (Measure.hausdorffMeasure 1 : Measure (localEuclideanBall z₀ r)) t := by
    rw [← himage]
    exact isometry_subtype_coe.hausdorffMeasure_image (Or.inl (by norm_num)) t
  have hL := (localEuclideanBall_coe_lipschitz z₀ hr hrsmall).hausdorffMeasure_image_le
    (d := 1) (by norm_num) t
  have hA := (localEuclideanBall_coe_antilipschitz z₀ hr hrsmall).le_hausdorffMeasure_image
    (d := 1) (by norm_num) t
  simpa only [ENNReal.rpow_one, hcomplex, ← hμ] using And.intro hL hA

theorem upperHalfPlane_I_sphere_in_small_euclidean_ball (r : ℝ) (hr : 0 ≤ r) :
    Metric.sphere UpperHalfPlane.I r ⊆
      localEuclideanBall UpperHalfPlane.I (Real.sinh r + Real.cosh r - 1) := by
  intro z hz
  have hrad := UpperHalfPlane.dist_eq_iff_dist_coe_center_eq.mp hz
  simp only [UpperHalfPlane.I_im, one_mul] at hrad
  have hcenter := UpperHalfPlane.dist_self_center UpperHalfPlane.I r
  simp only [UpperHalfPlane.I_im, one_mul] at hcenter
  have htri := dist_triangle (z : ℂ) (UpperHalfPlane.I.center r : ℂ) (UpperHalfPlane.I : ℂ)
  rw [hrad, dist_comm (UpperHalfPlane.I.center r : ℂ), hcenter] at htri
  exact htri.trans_eq (by ring)

end CurveComplex.Hyperbolic
