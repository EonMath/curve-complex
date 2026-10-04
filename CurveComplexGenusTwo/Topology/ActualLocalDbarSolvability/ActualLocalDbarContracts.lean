import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Complex.CauchyIntegral

open scoped ContDiff Distributions
open TopologicalSpace MeasureTheory

namespace CanonicalDimensionTwo.LocalDbar

/-- The literal plane Wirtinger derivative, with the same normalization as
`SameAtlasAnalyticCohomology.chartDbar`. -/
noncomputable def dbar (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I) / 2

/-- Complex-linear test-function ∂̄. Mathlib's LF topology and its actual
continuous derivative maps are retained. -/
noncomputable def testDbar (Ω : Opens ℂ) :
    TestFunction Ω ℂ ⊤ →L[ℂ] TestFunction Ω ℂ ⊤ :=
  (TestFunction.postcompCLM ((2 : ℂ)⁻¹ • ContinuousLinearMap.id ℂ ℂ)).comp
    (TestFunction.lineDerivCLM (Ω := Ω) (F := ℂ) (n := ⊤) (k := ⊤) ℂ (1 : ℂ) +
      (TestFunction.postcompCLM (Complex.I • ContinuousLinearMap.id ℂ ℂ)).comp
        (TestFunction.lineDerivCLM (Ω := Ω) (F := ℂ) (n := ⊤) (k := ⊤) ℂ Complex.I))

theorem testDbar_apply (Ω : Opens ℂ) (φ : TestFunction Ω ℂ ⊤) (z : ℂ) :
    testDbar Ω φ z = dbar φ z := by
  have hd : DifferentiableAt ℝ (φ : ℂ → ℂ) z :=
    (φ.contDiff.differentiable (by simp)).differentiableAt
  simp [testDbar, dbar, hd.lineDeriv_eq_fderiv, div_eq_mul_inv]
  ring


/-- Unproved source-facing disk solvability interface; McMullen Thm 8.2.
No global smoothness across the boundary of the disk is asserted. -/
def ActualLocalDbarSolvabilityStatement : Prop :=
  ∀ (c : ℂ) (R : ℝ), 0 < R → ∀ g : ℂ → ℂ,
    ContDiffOn ℝ ∞ g (Metric.ball c R) →
      ∃ F : ℂ → ℂ, ContDiffOn ℝ ∞ F (Metric.ball c R) ∧
        ∀ z ∈ Metric.ball c R, dbar F z = g z

/-- Unproved local Weyl interface for the actual continuous complex dual of
Mathlib's compactly supported smooth tests. The represented current uses
d(bar z) wedge dz = 2i dx wedge dy. -/
def ActualLocalWeylCurrentStatement : Prop :=
  ∀ (c : ℂ) (R : ℝ), 0 < R →
    ∀ T : TestFunction (⟨Metric.ball c R, Metric.isOpen_ball⟩ : Opens ℂ) ℂ ⊤ →L[ℂ] ℂ,
      (∀ φ, T (testDbar _ φ) = 0) →
        ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h (Metric.ball c R) ∧
          ∀ φ : TestFunction (⟨Metric.ball c R, Metric.isOpen_ball⟩ : Opens ℂ) ℂ ⊤,
            T φ = ∫ z : ℂ, (2 * Complex.I) * φ z * h z

end CanonicalDimensionTwo.LocalDbar
