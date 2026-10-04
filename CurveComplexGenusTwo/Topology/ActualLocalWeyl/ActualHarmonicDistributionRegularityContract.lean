import Mathlib.Analysis.Distribution.Distribution

open scoped ContDiff Distributions
open TopologicalSpace MeasureTheory

namespace CanonicalDimensionTwo.LocalDbar

/-- Pending source review and proof: the disk-local smooth-representative
consequence of the harmonic-distribution regularity assertion in McMullen,
printed page 82. The derivative maps and distribution topology are Mathlib's.
This declaration only defines the outstanding proposition. -/
def ActualDiskHarmonicDistributionSmoothRepresentativeStatement : Prop :=
  ∀ (c : ℂ) (R : ℝ), 0 < R →
    ∀ D : Distribution (⟨Metric.ball c R, Metric.isOpen_ball⟩ : Opens ℂ) ℂ ⊤,
      Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (1 : ℂ)
          (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (1 : ℂ) D) +
        Distribution.lineDerivCLM (n := ⊤) (k := ⊤) Complex.I
          (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) Complex.I D) = 0 →
      ∃ g : ℂ → ℂ, ContDiffOn ℝ ∞ g (Metric.ball c R) ∧
        D = Distribution.ofFun
          (⟨Metric.ball c R, Metric.isOpen_ball⟩ : Opens ℂ) g volume ⊤

end CanonicalDimensionTwo.LocalDbar
