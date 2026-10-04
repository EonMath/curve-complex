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

open scoped Manifold ContDiff Bundle Topology
open Bundle Set Function

set_option backward.isDefEq.respectTransparency false in
theorem actual_chart_solution_is_integral_curve_on
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (X : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x) (p : E)
    (f : ℝ → ℂ) (s : Set ℝ) (hs : IsOpen s)
    (hf : ∀ t ∈ s, HasDerivAt f
      (tangentCoordChange 𝓘(ℝ,ℂ) ((extChartAt 𝓘(ℝ,ℂ) p).symm (f t)) p
        ((extChartAt 𝓘(ℝ,ℂ) p).symm (f t))
        (X ((extChartAt 𝓘(ℝ,ℂ) p).symm (f t)))) t)
    (hinside : ∀ t ∈ s, f t ∈ (extChartAt 𝓘(ℝ,ℂ) p).target) :
    IsMIntegralCurveOn ((extChartAt 𝓘(ℝ,ℂ) p).symm ∘ f) X s := by
  intro t ht
  let x : E := (extChartAt 𝓘(ℝ,ℂ) p).symm (f t)
  have hx : x ∈ (extChartAt 𝓘(ℝ,ℂ) p).source :=
    (extChartAt 𝓘(ℝ,ℂ) p).map_target (hinside t ht)
  have hxx := mem_extChartAt_source (I := 𝓘(ℝ,ℂ)) x
  apply HasMFDerivAt.hasMFDerivWithinAt
  refine ⟨(continuousAt_extChartAt_symm'' (hinside t ht)).comp
    (hf t ht).continuousAt, HasDerivWithinAt.hasFDerivWithinAt ?_⟩
  simp only [mfld_simps, hasDerivWithinAt_univ]
  change HasDerivAt ((extChartAt 𝓘(ℝ,ℂ) x ∘
    (extChartAt 𝓘(ℝ,ℂ) p).symm) ∘ f) (X x) t
  rw [← tangentCoordChange_self (I := 𝓘(ℝ,ℂ)) (x := x) (z := x)
      (v := X x) hxx,
    ← tangentCoordChange_comp (x := p) ⟨⟨hxx, hx⟩, hxx⟩]
  apply HasFDerivAt.comp_hasDerivAt _ _ (hf t ht)
  apply HasFDerivWithinAt.hasFDerivAt (s := Set.range 𝓘(ℝ,ℂ)) _ (by simp)
  rw [← (extChartAt 𝓘(ℝ,ℂ) p).right_inv (hinside t ht)]
  exact hasFDerivWithinAt_tangentCoordChange ⟨hx, hxx⟩

#print axioms actual_chart_solution_is_integral_curve_on
