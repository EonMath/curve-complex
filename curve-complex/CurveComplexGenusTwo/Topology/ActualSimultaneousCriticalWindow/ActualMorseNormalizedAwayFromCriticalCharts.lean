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
open Set Bundle

def actual_critical_chart_complement_band
    {E : Type} [TopologicalSpace E] (F : E → ℝ) (S : Finset E)
    (c : E → OpenPartialHomeomorph E ℂ) (ρ : E → ℝ) (v ε : ℝ) : Set E :=
  {x | F x ∈ Icc (v - ε) (v + ε) ∧
    ∀ q ∈ S, x ∉ interior {y : E | y ∈ (c q).source ∧ ‖c q y‖ ≤ ρ q}}

theorem actual_critical_chart_complement_band_compact
    {E : Type} [TopologicalSpace E] [CompactSpace E]
    (F : E → ℝ) (hF : Continuous F) (S : Finset E)
    (c : E → OpenPartialHomeomorph E ℂ) (ρ : E → ℝ) (v ε : ℝ) :
    IsCompact (actual_critical_chart_complement_band F S c ρ v ε) := by
  have hclosed : IsClosed
      ({x | F x ∈ Icc (v - ε) (v + ε)} ∩
        ⋂ q ∈ (S : Set E),
          (interior {y : E | y ∈ (c q).source ∧ ‖c q y‖ ≤ ρ q})ᶜ) :=
    (isClosed_Icc.preimage hF).inter
      (isClosed_biInter (fun _ _ => isOpen_interior.isClosed_compl))
  have heq : actual_critical_chart_complement_band F S c ρ v ε =
      {x | F x ∈ Icc (v - ε) (v + ε)} ∩
        ⋂ q ∈ (S : Set E),
          (interior {y : E | y ∈ (c q).source ∧ ‖c q y‖ ≤ ρ q})ᶜ := by
    ext x
    simp [actual_critical_chart_complement_band]
  rw [heq]
  exact hclosed.isCompact

