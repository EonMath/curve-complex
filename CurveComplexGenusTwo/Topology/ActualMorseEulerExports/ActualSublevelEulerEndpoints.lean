import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualPairIntegralEulerAdditivity
import CurveComplexGenusTwo.Topology.ActualSimultaneousCriticalWindow.ActualMorseCompleteContinuousFlow
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualMorseGlobalGradientEnergy
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualMorseFiniteCriticalSet
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Topology.Homotopy.Equiv
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualRelativeDeformationVanishing
import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseHelpers

open CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz

theorem actual_integral_singular_homology_zero_of_isEmpty
    (X : Type) [TopologicalSpace X] [IsEmpty X] (n : ℕ) : IsZero (H X n) := by
  cases n with
  | zero =>
      have hz : IsZero (∐ fun _ : X => ModuleCat.of ℤ ℤ) := by
        apply (IsZero.iff_id_eq_zero _).mpr
        apply Sigma.hom_ext
        intro i
        exact isEmptyElim i
      exact hz.of_iso
        (AlgebraicTopology.singularHomologyFunctorZeroOfTotallyDisconnectedSpace
          (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) (TopCat.of X))
  | succ n =>
      exact AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
        (ModuleCat ℤ) (n + 1) (ModuleCat.of ℤ ℤ) (TopCat.of X) (by omega)
