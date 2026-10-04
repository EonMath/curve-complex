import CurveComplexGenusTwo.Hyperbolic.CompactSegmentParametrization
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactRightAngleMetric

namespace CurveComplex.Hyperbolic

noncomputable def positiveDilationIsometry (a : {x : ℝ // 0 < x}) : H2 ≃ᵢ H2 where
  toFun z := a • z
  invFun z := (⟨a.val⁻¹, inv_pos.mpr a.property⟩ : {x : ℝ // 0 < x}) • z
  left_inv z := by
    apply UpperHalfPlane.ext_re_im <;>
      simp only [UpperHalfPlane.pos_real_re, UpperHalfPlane.pos_real_im] <;>
      field_simp [ne_of_gt a.property]
  right_inv z := by
    apply UpperHalfPlane.ext_re_im <;>
      simp only [UpperHalfPlane.pos_real_re, UpperHalfPlane.pos_real_im] <;>
      field_simp [ne_of_gt a.property]
  isometry_toFun := UpperHalfPlane.isometry_pos_mul a

theorem exists_vertex_normalizing_isometry (p q : H2) :
    ∃ e : H2 ≃ᵢ H2, (e p).re = 0 ∧ (e p).im = 1 ∧ (e q).re = 0 := by
  obtain ⟨f, hp, hq⟩ := exists_pair_vertical_isometry p q
  let a : {x : ℝ // 0 < x} := ⟨(f p).im⁻¹, inv_pos.mpr (f p).im_pos⟩
  refine ⟨f.trans (positiveDilationIsometry a), ?_, ?_, ?_⟩
  · change (a • f p).re = 0
    simp only [UpperHalfPlane.pos_real_re, hp, mul_zero]
  · change (a • f p).im = 1
    simp only [UpperHalfPlane.pos_real_im]
    exact inv_mul_cancel₀ (ne_of_gt (f p).im_pos)
  · change (a • f q).re = 0
    simp only [UpperHalfPlane.pos_real_re, hq, mul_zero]

theorem actual_right_angle_vertex_normalization (q p r : H2)
    (h : IsRightAngle q p r) (hqp : q ≠ p) :
    ∃ e : H2 ≃ᵢ H2, (e p).re = 0 ∧ (e p).im = 1 ∧
      (e q).re = 0 ∧ (e r).re ^ 2 + (e r).im ^ 2 = 1 := by
  obtain ⟨e, hp, hi, hq⟩ := exists_vertex_normalizing_isometry p q
  exact ⟨e, hp, hi, hq,
    right_angle_unit_semicircle_of_normalized_isometry q p r h e hp hi hq hqp⟩

end CurveComplex.Hyperbolic
