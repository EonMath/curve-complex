import CurveComplexGenusTwo.Topology.ActualLocalDbarSolvability.ActualLocalDbarContracts
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

open scoped ContDiff Convolution
open MeasureTheory

namespace CanonicalDimensionTwo.LocalDbar

theorem locallyIntegrable_complex_inv :
    LocallyIntegrable (fun z : ℂ => z⁻¹) volume := by
  refine locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1)
    (by simp [Complex.finrank_real_complex])
    (by norm_num [Complex.finrank_real_complex]) ?_ ?_
  · filter_upwards with z
    simp [norm_inv, Real.rpow_neg_one]
  · exact measurable_inv.aestronglyMeasurable

theorem contDiff_inv_convolution {g : ℂ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    ContDiff ℝ ∞ ((fun z : ℂ => z⁻¹) ⋆[ContinuousLinearMap.mul ℝ ℂ] g) := by
  exact hc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
    locallyIntegrable_complex_inv hg

theorem hasFDerivAt_inv_convolution {g : ℂ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (z : ℂ) :
    HasFDerivAt ((fun w : ℂ => w⁻¹) ⋆[ContinuousLinearMap.mul ℝ ℂ] g)
      (((fun w : ℂ => w⁻¹) ⋆[(ContinuousLinearMap.mul ℝ ℂ).precompR ℂ]
        fderiv ℝ g) z) z := by
  exact hc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
    locallyIntegrable_complex_inv (hg.of_le (by simp)) z

theorem fderiv_inv_convolution_apply {g : ℂ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (z v : ℂ) :
    fderiv ℝ ((fun w : ℂ => w⁻¹) ⋆[ContinuousLinearMap.mul ℝ ℂ] g) z v =
      ∫ w : ℂ, w⁻¹ * fderiv ℝ g (z - w) v := by
  rw [(hasFDerivAt_inv_convolution hg hc z).fderiv]
  rw [convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℂ)
    locallyIntegrable_complex_inv (hc.fderiv ℝ)
    ((hg.of_le (by simp) : ContDiff ℝ 1 g).continuous_fderiv one_ne_zero)]
  rfl

theorem integrable_inv_mul_fderiv {g : ℂ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (z v : ℂ) :
    Integrable (fun w : ℂ => w⁻¹ * fderiv ℝ g (z - w) v) := by
  exact (hc.fderiv_apply ℝ v).convolutionExists_right (ContinuousLinearMap.mul ℝ ℂ)
    locallyIntegrable_complex_inv
    (((hg.of_le (by simp) : ContDiff ℝ 1 g).continuous_fderiv one_ne_zero).clm_apply
      continuous_const) z

theorem dbar_inv_convolution {g : ℂ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (z : ℂ) :
    dbar ((fun w : ℂ => w⁻¹) ⋆[ContinuousLinearMap.mul ℝ ℂ] g) z =
      ∫ w : ℂ, w⁻¹ * dbar g (z - w) := by
  rw [dbar, fderiv_inv_convolution_apply hg hc, fderiv_inv_convolution_apply hg hc]
  rw [← integral_const_mul, ← integral_add (integrable_inv_mul_fderiv hg hc z 1)
    ((integrable_inv_mul_fderiv hg hc z Complex.I).const_mul Complex.I),
    ← integral_div]
  apply integral_congr_ae
  filter_upwards with w
  simp only [dbar]
  ring

theorem dbar_const_mul {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (a : ℂ) :
    dbar (fun w => a * f w) z = a * dbar f z := by
  simp only [dbar, fderiv_const_mul hf, smul_apply, smul_eq_mul]
  ring

theorem contDiff_pi_inv_integral {g : ℂ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    ContDiff ℝ ∞ (fun z : ℂ =>
      (Real.pi : ℂ)⁻¹ * ∫ w : ℂ, w⁻¹ * g (z - w)) := by
  exact contDiff_const.mul (contDiff_inv_convolution hg hc)

theorem dbar_pi_inv_integral {g : ℂ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (z : ℂ) :
    dbar (fun u : ℂ => (Real.pi : ℂ)⁻¹ * ∫ w : ℂ, w⁻¹ * g (u - w)) z =
      (Real.pi : ℂ)⁻¹ * ∫ w : ℂ, w⁻¹ * dbar g (z - w) := by
  change dbar (fun u => (Real.pi : ℂ)⁻¹ *
    ((fun w : ℂ => w⁻¹) ⋆[ContinuousLinearMap.mul ℝ ℂ] g) u) z = _
  rw [dbar_const_mul (hasFDerivAt_inv_convolution hg hc z).differentiableAt,
    dbar_inv_convolution hg hc z]

end CanonicalDimensionTwo.LocalDbar
