import CurveComplexGenusTwo.Topology.ActualLocalDbarSolvability.ActualLocalDbarContracts

open TopologicalSpace MeasureTheory Filter
open scoped ContDiff Distributions Topology

namespace CanonicalDimensionTwo.LocalDbar

/-- The literal local cutoff-to-contour identity. With g_01=h and
F_i=sum_j rho_j*g_ij, the local Dolbeault coefficient is -h*dbar(rho_0).
The orientation is d(bar z) wedge dz = 2i dx wedge dy. -/
def ActualPlanarCutoffContourStatement : Prop :=
  ∀ (Ω : Opens ℂ) (a : ℂ) (_ha : a ∈ Ω)
    (χ : TestFunction Ω ℝ ⊤),
    (∀ᶠ z in 𝓝 a, χ z = 1) →
    ∀ f : ℂ → ℂ, AnalyticOnNhd ℂ f ((Ω : Set ℂ) \ {a}) →
    ∀ (R : ℝ), 0 < R → Metric.closedBall a R ⊆ Ω →
      (∫ z : ℂ, -(2 * Complex.I) *
        dbar (fun w : ℂ => (χ w : ℂ)) z * f z) =
        circleIntegral f a R

end CanonicalDimensionTwo.LocalDbar
