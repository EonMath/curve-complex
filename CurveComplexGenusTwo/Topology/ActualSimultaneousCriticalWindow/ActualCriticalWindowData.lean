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
open Set Bundle CategoryTheory
open CurveComplexGenusTwo.CWHurewicz

/-!
REVIEW-ONLY scaffold. This file is deliberately excluded from the frozen release.
Source: Milnor, Morse Theory, §3, Theorem 3.2 and Remark 3.3 (printed pp. 14–19).
The relative-map formulation also uses singular excision. Several critical
points may have the SAME value. Their actual chart regions are the domain of
the literal inclusion map, not abstract homology certificates.
-/

def actualCriticalWindowQuadratic (k : Fin 3) (z : ℂ) : ℝ :=
  if k = 0 then z.re ^ 2 + z.im ^ 2
  else if k = 1 then z.re ^ 2 - z.im ^ 2
  else -(z.re ^ 2 + z.im ^ 2)

def actualCriticalChartRegion {E : Type} [TopologicalSpace E]
    (c : OpenPartialHomeomorph E ℂ) (ρ : ℝ) : Set E :=
  {x | x ∈ c.source ∧ ‖c x‖ ≤ ρ}

def actualCriticalWindowLocalUpper {E : Type} [TopologicalSpace E]
    (F : E → ℝ) (S : Finset E) (c : E → OpenPartialHomeomorph E ℂ)
    (ρ : E → ℝ) (v ε : ℝ) : Set E :=
  {x | (∃ q ∈ S, x ∈ actualCriticalChartRegion (c q) (ρ q)) ∧ F x ≤ v + ε}

def actualCriticalWindowLocalLower {E : Type} [TopologicalSpace E]
    (F : E → ℝ) (S : Finset E) (c : E → OpenPartialHomeomorph E ℂ)
    (ρ : E → ℝ) (v ε : ℝ) :
    Set (actualCriticalWindowLocalUpper F S c ρ v ε) :=
  {x | F x.1 ≤ v - ε}

def actualCriticalWindowFullLower {E : Type} [TopologicalSpace E]
    (F : E → ℝ) (v ε : ℝ) : Set {x : E // F x ≤ v + ε} :=
  {x | F x.1 ≤ v - ε}

def actualCriticalWindowInclusion {E : Type} [TopologicalSpace E]
    (F : E → ℝ) (S : Finset E) (c : E → OpenPartialHomeomorph E ℂ)
    (ρ : E → ℝ) (v ε : ℝ) :
    C(actualCriticalWindowLocalUpper F S c ρ v ε, {x : E // F x ≤ v + ε}) :=
  ⟨fun x => ⟨x.1, x.2.2⟩, continuous_subtype_val.subtype_mk _⟩

