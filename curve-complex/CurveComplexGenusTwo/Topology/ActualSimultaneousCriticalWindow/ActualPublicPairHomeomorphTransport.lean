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
/- Exact visibility lift of the existing checked scratch proof.
   Proof body is unchanged; the export has a new public name. -/

open CategoryTheory

theorem actual_pairRelativeHomologyMap_homeomorph_isIso
    (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (e : X ≃ₜ Y)
    (hAB : ∀ x, x ∈ A ↔ e x ∈ B) (n : ℕ) :
    IsIso (CurveComplexGenusTwo.CWHurewicz.pairRelativeHomologyMap A B
      ⟨e, e.continuous⟩ (fun x hx => (hAB x).mp hx) n) := by
  let eMap : C(X, Y) := ⟨e, e.continuous⟩
  let eInvMap : C(Y, X) := ⟨e.symm, e.symm.continuous⟩
  let f := CurveComplexGenusTwo.CWHurewicz.pairRelativeHomologyMap A B
    eMap (fun x hx => (hAB x).mp hx) n
  let g := CurveComplexGenusTwo.CWHurewicz.pairRelativeHomologyMap B A
    eInvMap (fun y hy => (hAB (e.symm y)).mpr (by simpa using hy)) n
  have hfg : f ≫ g = 𝟙 _ := by
    rw [← CurveComplexGenusTwo.CWHurewicz.pairRelativeHomologyMap_comp]
    have hmap : eInvMap.comp eMap =
        ContinuousMap.id X := by
      ext x
      exact e.symm_apply_apply x
    simpa only [hmap] using
      (CurveComplexGenusTwo.CWHurewicz.pairRelativeHomologyMap_id A n)
  have hgf : g ≫ f = 𝟙 _ := by
    rw [← CurveComplexGenusTwo.CWHurewicz.pairRelativeHomologyMap_comp]
    have hmap : eMap.comp eInvMap =
        ContinuousMap.id Y := by
      ext y
      exact e.apply_symm_apply y
    simpa only [hmap] using
      (CurveComplexGenusTwo.CWHurewicz.pairRelativeHomologyMap_id B n)
  exact ⟨g, hfg, hgf⟩

#print axioms actual_pairRelativeHomologyMap_homeomorph_isIso
