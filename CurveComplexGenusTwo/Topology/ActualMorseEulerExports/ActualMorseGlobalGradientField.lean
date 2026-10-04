import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualMorseGradientTangentLocal

open scoped Manifold ContDiff Bundle
open Bundle Set

theorem actual_finite_supported_chart_gradient_field_smooth
    {E ι : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E] [Fintype ι]
    (p : ι → E) (b : ι → E → ℝ)
    (hb : ∀ i, ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ (b i))
    (hs : ∀ i, tsupport (b i) ⊆ (chartAt ℂ (p i)).source)
    (F : E → ℝ) (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F) :
    ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x
        (∑ i, b i x •
          (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) (p i)).symmL ℝ x
            (gradient (fun z => F ((chartAt ℂ (p i)).symm z))
              ((chartAt ℂ (p i)) x)))) := by
  apply ContMDiff.sum_section (s := Finset.univ)
  intro i hi
  exact actual_supported_chart_gradient_tangent_smooth (p i) F hF
    (b i) (hb i) (hs i)

