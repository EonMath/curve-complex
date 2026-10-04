import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace CurveComplex.Hyperbolic
open Matrix
open scoped MatrixGroups ContDiff

theorem real_smooth_gl_upper_half_plane_formula (g : GL (Fin 2) ℝ) :
    ContDiffOn ℝ ∞ (fun z : ℂ => UpperHalfPlane.σ g
      (UpperHalfPlane.num g z / UpperHalfPlane.denom g z)) {z : ℂ | 0 < z.im} := by
  have hn : ContDiff ℝ ∞ (UpperHalfPlane.num g) := by
    exact (contDiff_const.mul contDiff_id).add contDiff_const
  have hd : ContDiff ℝ ∞ (UpperHalfPlane.denom g) := by
    exact (contDiff_const.mul contDiff_id).add contDiff_const
  have hfrac : ContDiffOn ℝ ∞ (fun z : ℂ => UpperHalfPlane.num g z /
      UpperHalfPlane.denom g z) {z : ℂ | 0 < z.im} :=
    by
      simpa only [div_eq_mul_inv, Pi.inv_apply] using! hn.contDiffOn.mul (hd.contDiffOn.inv
        (fun z hz => UpperHalfPlane.denom_ne_zero_of_im g (ne_of_gt hz)))
  unfold UpperHalfPlane.σ
  split_ifs
  · simpa using hfrac
  · exact Complex.conjCLE.contDiff.comp_contDiffOn hfrac

theorem real_smooth_gl_upper_half_plane_action (g : GL (Fin 2) ℝ) :
    ContDiffOn ℝ ∞ (fun z : ℂ => ((g • UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ))
      {z : ℂ | 0 < z.im} := by
  apply (real_smooth_gl_upper_half_plane_formula g).congr
  intro z hz
  rw [UpperHalfPlane.coe_smul, UpperHalfPlane.ofComplex_apply_of_im_pos hz]

end CurveComplex.Hyperbolic
