import CurveComplexGenusTwo.Topology.ActualSmoothMorseNormalForm.ActualMorseChartPullbackSmooth
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Symmetric

open scoped Manifold ContDiff
open Set InnerProductSpace

theorem actual_complex_scalar_gradient_derivative_pairing
    (f : ℂ → ℝ) (z : ℂ) (hf : ContDiffAt ℝ 2 f z) (v w : ℂ) :
    ⟪(fderiv ℝ (gradient f) z) v, w⟫_ℝ =
      (fderiv ℝ (fderiv ℝ f) z) v w := by
  have hg : DifferentiableAt ℝ (gradient f) z := by
    change DifferentiableAt ℝ ((toDual ℝ ℂ).symm ∘ fderiv ℝ f) z
    exact (toDual ℝ ℂ).symm.toContinuousLinearMap.differentiableAt.comp z
      ((hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt
        (by norm_num))
  have hder : fderiv ℝ (fderiv ℝ f) z =
      (toDual ℝ ℂ).toContinuousLinearMap.comp (fderiv ℝ (gradient f) z) := by
    have hh := (toDual ℝ ℂ).toContinuousLinearMap.hasFDerivAt.comp z hg.hasFDerivAt
    change HasFDerivAt ((toDual ℝ ℂ) ∘ gradient f)
      ((toDual ℝ ℂ).toContinuousLinearMap.comp (fderiv ℝ (gradient f) z)) z at hh
    rw [toDual_comp_gradient] at hh
    exact hh.fderiv
  rw [hder]
  rfl

#print axioms actual_complex_scalar_gradient_derivative_pairing

theorem actual_complex_scalar_gradient_derivative_isSymmetric
    (f : ℂ → ℝ) (z : ℂ) (hf : ContDiffAt ℝ 2 f z) :
    ((fderiv ℝ (gradient f) z) : ℂ →ₗ[ℝ] ℂ).IsSymmetric := by
  intro v w
  change ⟪(fderiv ℝ (gradient f) z) v, w⟫_ℝ =
    ⟪v, (fderiv ℝ (gradient f) z) w⟫_ℝ
  calc
    ⟪(fderiv ℝ (gradient f) z) v, w⟫_ℝ =
        (fderiv ℝ (fderiv ℝ f) z) v w :=
      actual_complex_scalar_gradient_derivative_pairing f z hf v w
    _ = (fderiv ℝ (fderiv ℝ f) z) w v :=
      hf.isSymmSndFDerivAt (by norm_num) v w
    _ = ⟪(fderiv ℝ (gradient f) z) w, v⟫_ℝ :=
      (actual_complex_scalar_gradient_derivative_pairing f z hf w v).symm
    _ = ⟪v, (fderiv ℝ (gradient f) z) w⟫_ℝ := real_inner_comm _ _

#print axioms actual_complex_scalar_gradient_derivative_isSymmetric

theorem actual_same_atlas_chart_gradient_derivative_isSymmetric
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (F : E → ℝ) (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F)
    (p x : E) (hx : x ∈ (chartAt ℂ p).source) :
    ((fderiv ℝ (gradient (fun z => F ((chartAt ℂ p).symm z)))
      ((chartAt ℂ p) x)) : ℂ →ₗ[ℝ] ℂ).IsSymmetric := by
  apply actual_complex_scalar_gradient_derivative_isSymmetric
  exact (((actual_smooth_scalar_chart_pullback_contDiffOn_infty p F hF)
    ((chartAt ℂ p) x) ((chartAt ℂ p).map_source hx)).contDiffAt
      ((chartAt ℂ p).open_target.mem_nhds ((chartAt ℂ p).map_source hx))).of_le
    (by norm_num)

#print axioms actual_same_atlas_chart_gradient_derivative_isSymmetric

theorem actual_nondegenerate_complex_scalar_has_nonzero_quadratic_direction
    (f : ℂ → ℝ) (z : ℂ) (hf : ContDiffAt ℝ 2 f z)
    (hdet : (fderiv ℝ (gradient f) z).det ≠ 0) :
    ∃ v : ℂ, ⟪(fderiv ℝ (gradient f) z) v, v⟫_ℝ ≠ 0 := by
  by_contra hnone
  push Not at hnone
  have hz : ((fderiv ℝ (gradient f) z) : ℂ →ₗ[ℝ] ℂ) = 0 :=
    (actual_complex_scalar_gradient_derivative_isSymmetric f z hf).inner_map_self_eq_zero.mp
      hnone
  have hzero : fderiv ℝ (gradient f) z = 0 := by
    ext v
    exact congrArg (fun L : ℂ →ₗ[ℝ] ℂ => L v) hz
  apply hdet
  rw [hzero]
  change (0 : ℂ →ₗ[ℝ] ℂ).det = 0
  rw [LinearMap.det_zero, Complex.finrank_real_complex]
  norm_num

#print axioms actual_nondegenerate_complex_scalar_has_nonzero_quadratic_direction
