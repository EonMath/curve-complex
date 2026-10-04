import Mathlib

namespace CurveComplex.Hyperbolic
open Set MeasureTheory
open scoped MeasureTheory NNReal ENNReal UpperHalfPlane

theorem real_line_hausdorff_area_zero :
    (Measure.hausdorffMeasure 2 : Measure ℝ) univ = 0 := by
  have hc : (univ : Set ℝ) = ⋃ n : ℕ, Icc (-(n : ℝ)) n := by
    ext x
    simp only [mem_univ, mem_iUnion, mem_Icc, true_iff]
    obtain ⟨n, hn⟩ := exists_nat_gt |x|
    exact ⟨n, by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
  rw [hc]
  apply measure_iUnion_null
  intro n
  have hf : (Measure.hausdorffMeasure 1 : Measure ℝ) (Icc (-(n : ℝ)) n) ≠ ∞ := by
    rw [MeasureTheory.hausdorffMeasure_real, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  exact (Measure.hausdorffMeasure_zero_or_top (by norm_num : (1 : ℝ) < 2)
    (Icc (-(n : ℝ)) n)).resolve_right hf

theorem vertical_geodesic_hausdorff_area_zero (c : ℝ) :
    (Measure.hausdorffMeasure 2 : Measure UpperHalfPlane) {z | z.re = c} = 0 := by
  let f : ℝ → UpperHalfPlane := fun y => ⟨⟨c, Real.exp y⟩, Real.exp_pos y⟩
  have hi : Isometry f := UpperHalfPlane.isometry_vertical_line c
  have hf : f '' univ = {z | z.re = c} := by
    ext z; constructor
    · rintro ⟨y, _, rfl⟩; rfl
    · intro hz
      refine ⟨Real.log z.im, mem_univ _, ?_⟩
      apply UpperHalfPlane.ext_re_im
      · exact hz.symm
      · exact Real.exp_log z.im_pos
  have ha := hi.hausdorffMeasure_image (d := 2) (Or.inl (by norm_num)) univ
  rw [hf, real_line_hausdorff_area_zero] at ha
  exact ha

theorem isometric_vertical_geodesic_normalized_area_zero (c : ℝ) (e : UpperHalfPlane ≃ᵢ UpperHalfPlane) :
    (μHE[2] : Measure UpperHalfPlane) (e '' {z | z.re = c}) = 0 := by
  have ha := e.isometry.hausdorffMeasure_image (d := 2) (Or.inl (by norm_num)) {z | z.re = c}
  rw [vertical_geodesic_hausdorff_area_zero] at ha
  unfold Measure.euclideanHausdorffMeasure
  simp only [Measure.smul_apply]
  norm_num only [Nat.cast_ofNat] at *
  rw [ha, smul_zero]

end CurveComplex.Hyperbolic
