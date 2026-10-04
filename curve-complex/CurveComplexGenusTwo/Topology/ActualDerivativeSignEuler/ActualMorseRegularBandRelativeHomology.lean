import CurveComplexGenusTwo.Topology.ActualDerivativeSignEuler.ActualMorseRegularSublevelDeformation
import CurveComplexGenusTwo.Topology.ActualDerivativeSignEuler.ActualRelativeDeformationVanishing

open scoped Manifold ContDiff Bundle Topology
open Bundle Set Function CategoryTheory CategoryTheory.Limits

theorem actual_normalized_regular_band_relative_homology_zero
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (F : E → ℝ) (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F)
    (Y : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (φ : Flow ℝ E) (hcurve : ∀ x, IsMIntegralCurve (fun t => φ t x) Y)
    (a₀ a b b₀ : ℝ) (ha : a₀ < a) (hab : a ≤ b) (hb : b < b₀)
    (hunit : ∀ x, F x ∈ Icc a₀ b₀ →
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F x))
        ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x) (Y x)) = 1)
    (n : ℕ) :
    IsZero (CurveComplexGenusTwo.CWHurewicz.relativeHomology
      {x : E // F x ≤ b} {x | F x.1 ≤ a} n) := by
  obtain ⟨r, H, _, hfix⟩ :=
    actual_normalized_regular_band_sublevel_deformation F hF Y φ hcurve
      a₀ a b b₀ ha hab hb hunit
  let i : C({x : E // F x ≤ a}, {x : E // F x ≤ b}) :=
    ⟨fun x => ⟨x.1, x.2.trans hab⟩, continuous_subtype_val.subtype_mk _⟩
  apply CurveComplexGenusTwo.CWHurewicz.actual_relativeHomology_zero_of_deformation_into_subspace
    {x : {x : E // F x ≤ b} | F x.1 ≤ a} (i.comp r)
    (fun x => (r x).2) H ?_ n
  intro t x hx
  change F (H (t, x)).1 ≤ a
  rw [hfix t x hx]
  exact hx
