import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualMorseGlobalGradientEnergy
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualMorseFiniteCriticalSet

open scoped Manifold ContDiff Bundle
open Bundle Set InnerProductSpace

/-- Criticality in one literal chart forces the actual manifold derivative to
vanish. The chart and tangent trivialization are the original input atlas. -/
theorem actual_scalar_mfderiv_zero_of_chart_gradient_zero
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (F : E → ℝ) (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F)
    (p x : E) (hx : x ∈ (chartAt ℂ p).source)
    (hgrad : gradient (fun z => F ((chartAt ℂ p).symm z)) ((chartAt ℂ p) x) = 0) :
    mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x = 0 := by
  let e := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) p
  have hbase : x ∈ e.baseSet := by simpa [e] using hx
  have hd : fderiv ℝ (fun z => F ((chartAt ℂ p).symm z)) ((chartAt ℂ p) x) = 0 := by
    rw [← toDual_gradient, hgrad, map_zero]
  ext v
  have hi := actual_chart_tangent_scalar_derivative_identity p x hx F hF
    (e.continuousLinearMapAt ℝ x v)
  rw [e.symmL_continuousLinearMapAt hbase, hd] at hi
  exact hi

/-- Every other literal chart sees the same zero gradient at a critical point;
this uses the actual scalar derivative identity, not chart replacement. -/
theorem actual_chart_gradient_zero_of_scalar_mfderiv_zero
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (F : E → ℝ) (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F)
    (x : E) (hd : mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x = 0)
    (p : E) (hx : x ∈ (chartAt ℂ p).source) :
    gradient (fun z => F ((chartAt ℂ p).symm z)) ((chartAt ℂ p) x) = 0 := by
  apply (toDual ℝ ℂ).injective
  rw [toDual_gradient, map_zero]
  ext v
  have hi := actual_chart_tangent_scalar_derivative_identity p x hx F hF v
  rw [hd, zero_apply, map_zero] at hi
  exact hi.symm

/-- The actual finite supported sum of chart gradients vanishes at every
critical point of F. The formula for the field is essential here. -/
theorem actual_finite_supported_chart_gradient_field_zero_at_critical
    {E ι : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E] [Fintype ι]
    (p : ι → E) (b : ι → E → ℝ)
    (hs : ∀ i, tsupport (b i) ⊆ (chartAt ℂ (p i)).source)
    (F : E → ℝ) (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F)
    (q x : E) (hx : x ∈ (chartAt ℂ q).source)
    (hgrad : gradient (fun z => F ((chartAt ℂ q).symm z)) ((chartAt ℂ q) x) = 0) :
    (∑ i, b i x •
      (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) (p i)).symmL ℝ x
        (gradient (fun z => F ((chartAt ℂ (p i)).symm z))
          ((chartAt ℂ (p i)) x))) = 0 := by
  classical
  have hd := actual_scalar_mfderiv_zero_of_chart_gradient_zero F hF q x hx hgrad
  apply Finset.sum_eq_zero
  intro i _
  by_cases hbi : b i x = 0
  · rw [hbi, zero_smul]
  · have hxi : x ∈ (chartAt ℂ (p i)).source := hs i (subset_tsupport (b i) hbi)
    rw [actual_chart_gradient_zero_of_scalar_mfderiv_zero F hF x hd (p i) hxi,
      map_zero, smul_zero]

/-- The retained finite Morse set is exactly the intrinsic critical set of
the same actual function, from chart criticality and positivity off that set. -/
theorem actual_retained_morse_set_eq_scalar_mfderiv_zero
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (F : E → ℝ) (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F)
    (Z : Finset E) (X : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (hcrit : ∀ x ∈ Z, ∃ p : E, x ∈ (chartAt ℂ p).source ∧
      gradient (fun z => F ((chartAt ℂ p).symm z)) ((chartAt ℂ p) x) = 0)
    (hup : ∀ x : E, x ∉ Z →
      0 < (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F x))
        ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x) (X x))) :
    (Z : Set E) = {x | mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x = 0} := by
  ext x
  constructor
  · intro hx
    obtain ⟨p, hxp, hp⟩ := hcrit x hx
    exact actual_scalar_mfderiv_zero_of_chart_gradient_zero F hF p x hxp hp
  · intro hx
    by_contra hn
    have hpos := hup x hn
    change mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x = 0 at hx
    rw [hx, zero_apply, map_zero] at hpos
    exact (lt_irrefl (0 : ℝ)) hpos

