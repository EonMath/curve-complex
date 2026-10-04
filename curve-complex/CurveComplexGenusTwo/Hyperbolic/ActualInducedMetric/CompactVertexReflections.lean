import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactVertexNormalization
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.VerticalReflectionCrossing

namespace CurveComplex.Hyperbolic
open scoped MatrixGroups

noncomputable def unitCircleReflectionEquiv : H2 ≃ᵢ H2 :=
  verticalReflectionEquiv.trans (IsometryEquiv.constSMul
    (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) ModularGroup.S))

theorem unitCircleReflection_coe (z : H2) :
    (unitCircleReflectionEquiv z : ℂ) = (star (z : ℂ))⁻¹ := by
  change ((ModularGroup.S • verticalReflectionEquiv z : H2) : ℂ) = _
  rw [UpperHalfPlane.modular_S_smul]
  change (-(verticalReflectionEquiv z : ℂ))⁻¹ = _
  congr 1
  apply Complex.ext
  · change -(verticalReflectionEquiv z).re = z.re
    rw [verticalReflection_re]
    ring
  · change -(verticalReflectionEquiv z).im = -z.im
    rw [verticalReflection_im]

theorem unitCircleReflection_re (z : H2) :
    (unitCircleReflectionEquiv z).re = z.re / ((z.re)^2 + (z.im)^2) := by
  change (unitCircleReflectionEquiv z : ℂ).re = _
  rw [unitCircleReflection_coe]
  simp only [Complex.star_def, Complex.inv_re, Complex.conj_re,
    Complex.normSq_conj, Complex.normSq_apply, Complex.conj_im,
    UpperHalfPlane.re, UpperHalfPlane.im]
  ring

theorem unitCircleReflection_im (z : H2) :
    (unitCircleReflectionEquiv z).im = z.im / ((z.re)^2 + (z.im)^2) := by
  change (unitCircleReflectionEquiv z : ℂ).im = _
  rw [unitCircleReflection_coe]
  simp only [Complex.star_def, Complex.inv_im, Complex.conj_im,
    Complex.normSq_conj, Complex.normSq_apply, Complex.conj_re,
    neg_neg, UpperHalfPlane.re, UpperHalfPlane.im]
  ring

theorem unitCircleReflection_fixed_iff (z : H2) :
    unitCircleReflectionEquiv z = z ↔ z.re ^ 2 + z.im ^ 2 = 1 := by
  constructor
  · intro h
    have hi := congrArg UpperHalfPlane.im h
    rw [unitCircleReflection_im] at hi
    have hd : z.re ^ 2 + z.im ^ 2 ≠ 0 := by nlinarith [z.im_pos]
    rw [div_eq_iff hd] at hi
    nlinarith [z.im_pos]
  · intro h
    apply UpperHalfPlane.ext_re_im
    · rw [unitCircleReflection_re, h, div_one]
    · rw [unitCircleReflection_im, h, div_one]

theorem unitCircleReflection_involutive : Function.Involutive unitCircleReflectionEquiv := by
  intro z
  apply UpperHalfPlane.ext
  simp only [unitCircleReflection_coe, Complex.star_def, map_inv₀,
    Complex.conj_conj, inv_inv]

theorem vertex_reflections_commute (z : H2) :
    unitCircleReflectionEquiv (verticalReflectionEquiv z) =
      verticalReflectionEquiv (unitCircleReflectionEquiv z) := by
  apply UpperHalfPlane.ext_re_im
  · simp only [unitCircleReflection_re, verticalReflection_re, verticalReflection_im,
      neg_sq, neg_div]
  · simp only [unitCircleReflection_im, verticalReflection_re, verticalReflection_im, neg_sq]

theorem unitCircleReflection_normSq (z : H2) :
    (unitCircleReflectionEquiv z).re ^ 2 +
      (unitCircleReflectionEquiv z).im ^ 2 =
        1 / (z.re ^ 2 + z.im ^ 2) := by
  rw [unitCircleReflection_re, unitCircleReflection_im]
  have hd : z.re ^ 2 + z.im ^ 2 ≠ 0 := by nlinarith [z.im_pos]
  field_simp

theorem unitCircleReflection_inner_iff_outer (z : H2) :
    (unitCircleReflectionEquiv z).re ^ 2 +
      (unitCircleReflectionEquiv z).im ^ 2 < 1 ↔
        1 < z.re ^ 2 + z.im ^ 2 := by
  rw [unitCircleReflection_normSq]
  have hd : 0 < z.re ^ 2 + z.im ^ 2 := by nlinarith [z.im_pos]
  rw [div_lt_iff₀ hd]
  simp only [one_mul]

end CurveComplex.Hyperbolic
