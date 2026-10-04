import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualMorseTangentDerivativeIdentity
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualMorseWeightedGradientPositive

open scoped Manifold ContDiff Bundle
open Bundle Set InnerProductSpace

theorem actual_finite_chart_gradient_field_energy
    {E ι : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E] [Fintype ι]
    (p : ι → E) (b : ι → E → ℝ)
    (hs : ∀ i, tsupport (b i) ⊆ (chartAt ℂ (p i)).source)
    (F : E → ℝ) (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F)
    (x : E) :
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F x))
      ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x)
        (∑ i, b i x •
          (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) (p i)).symmL ℝ x
            (gradient (fun z => F ((chartAt ℂ (p i)).symm z))
              ((chartAt ℂ (p i)) x)))) =
      ∑ i, b i x *
        ‖gradient (fun z => F ((chartAt ℂ (p i)).symm z))
          ((chartAt ℂ (p i)) x)‖ ^ 2 := by
  rw [map_sum]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hbi : b i x = 0
  · simp [hbi]
  · have hx : x ∈ (chartAt ℂ (p i)).source := by
      apply hs i
      exact subset_tsupport (b i) hbi
    rw [actual_chart_tangent_scalar_derivative_identity (p i) x hx F hF]
    have hdiff : DifferentiableAt ℝ
        (fun z : ℂ => F ((chartAt ℂ (p i)).symm z)) ((chartAt ℂ (p i)) x) := by
      have h := actual_smooth_scalar_chart_pullback_contDiffOn_infty (p i) F hF
      exact ((h _ ((chartAt ℂ (p i)).map_source hx)).contDiffAt
        ((chartAt ℂ (p i)).open_target.mem_nhds
          ((chartAt ℂ (p i)).map_source hx))).differentiableAt
        (by simp)
    rw [hdiff.hasGradientAt.fderiv_apply, real_inner_self_eq_norm_sq]

