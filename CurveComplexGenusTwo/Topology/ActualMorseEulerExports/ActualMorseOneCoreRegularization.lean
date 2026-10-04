import CurveComplexGenusTwo.Topology.ActualSmoothMorseNormalForm.ActualMorseChartPullbackSmooth
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualMorseGradientShift

open scoped Manifold ContDiff
open Set InnerProductSpace

theorem actual_morse_one_chart_core_nondegenerate
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (p : E) (F : E → ℝ)
    (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F)
    (b : E → ℝ) (U : Set E) (hU : IsOpen U)
    (hUb : ∀ x ∈ U, b x = 1)
    (r : ℝ) (hr : 0 < r) :
    let Ω : Set ℂ := (chartAt ℂ p).target ∩ (chartAt ℂ p).symm ⁻¹' U;
    ∃ c : ℂ, ‖c‖ < r ∧
      ∀ z ∈ Ω,
        gradient (fun w => F ((chartAt ℂ p).symm w) +
          b ((chartAt ℂ p).symm w) * (toDual ℝ ℂ c) w) z = 0 →
        (fderiv ℝ (gradient (fun w => F ((chartAt ℂ p).symm w) +
          b ((chartAt ℂ p).symm w) * (toDual ℝ ℂ c) w)) z).det ≠ 0 := by
  let Ω : Set ℂ := (chartAt ℂ p).target ∩ (chartAt ℂ p).symm ⁻¹' U
  have hΩ : IsOpen Ω := (chartAt ℂ p).isOpen_inter_preimage_symm hU
  have hΩtarget : Ω ⊆ (chartAt ℂ p).target := inter_subset_left
  have hchart : ContDiffOn ℝ 2 (fun z : ℂ => F ((chartAt ℂ p).symm z)) Ω :=
    (actual_smooth_scalar_chart_pullback_contDiffOn p F hF).mono hΩtarget
  have hbchart : ∀ z ∈ Ω, b ((chartAt ℂ p).symm z) = 1 := by
    intro z hz
    exact hUb _ hz.2
  exact actual_morse_small_shift_nondegenerate_on_plateau
    (fun z => F ((chartAt ℂ p).symm z))
    (fun z => b ((chartAt ℂ p).symm z)) Ω hΩ hchart hbchart r hr

