import CurveComplexGenusTwo.CWHurewicz.ExcisionDifferentialTransport
import CurveComplexGenusTwo.CWHurewicz.PairExactnessInterface
import CurveComplexGenusTwo.CWHurewicz.PairHomotopyInvariance
import CurveComplexGenusTwo.CWHurewicz.PairNaturality
import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseHelpers
import CurveComplexGenusTwo.Dictionary.Genus
import Mathlib.Algebra.Exact.Sequence
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Dynamics.Flow
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Separation.Regular

open scoped Manifold ContDiff Bundle
open Bundle Set

theorem actual_integral_curve_scalar_height_derivative
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (F : E → ℝ) (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F)
    (X : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (γ : ℝ → E) (t : ℝ)
    (hγ : IsMIntegralCurveAt γ X t) :
    HasDerivAt (F ∘ γ)
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (F (γ t)))
        ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F (γ t)) (X (γ t)))) t := by
  have hγt : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ,ℂ) γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X (γ t))) := by
    obtain ⟨s, hs, hcurve⟩ := Filter.Eventually.exists_mem hγ
    exact hcurve t (mem_of_mem_nhds hs)
  have hFt : MDifferentiableAt 𝓘(ℝ,ℂ) 𝓘(ℝ) F (γ t) :=
    hF.mdifferentiableAt (by simp)
  have hcomp := hFt.hasMFDerivAt.comp t hγt
  have hfderiv : HasFDerivAt (F ∘ γ)
      ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F (γ t)) ∘L
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X (γ t)))) t :=
    hcomp.hasFDerivAt
  have hderiv : HasDerivAt (F ∘ γ)
      (((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F (γ t)) ∘L
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X (γ t)))) 1) t :=
    (hasFDerivAt_iff_hasDerivAt (𝕜 := ℝ) (F := ℝ)).mp hfderiv
  have hdir : ((1 : ℝ →L[ℝ] ℝ).smulRight (X (γ t))) 1 = X (γ t) := by
    simp
  have heq : ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F (γ t)) ∘L
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X (γ t)))) 1 =
      (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F (γ t)) (X (γ t)) := by
    simp [hdir]
  rw [heq] at hderiv
  exact hderiv

