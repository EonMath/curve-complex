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
import CurveComplexGenusTwo.Topology.ActualSimultaneousCriticalWindow.ActualMorseContinuousLocalFlow

open scoped Manifold ContDiff Bundle Topology
open Bundle Set Function Metric Filter

theorem actual_smooth_complex_field_uniform_local_time
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E] [CompactSpace E]
    (X : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (hX : ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (X x))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : E, ∃ γ : ℝ → E,
      γ 0 = x ∧ IsMIntegralCurveOn γ X (Ioo (-ε) ε) := by
  classical
  have hlocal := actual_smooth_complex_field_has_continuous_local_flow X hX
  choose U e Φ hU hp he hcont hcurve using hlocal
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU (by
    intro x _
    exact mem_iUnion.mpr ⟨x, hp x⟩)
  have hmin : ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ s, ε ≤ e p := by
    clear hs
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert p s hps ih =>
      obtain ⟨ε, hε, hbound⟩ := ih
      refine ⟨min ε (e p), lt_min hε (he p), ?_⟩
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hbound q hq)
  obtain ⟨ε, hε, hbound⟩ := hmin
  refine ⟨ε, hε, ?_⟩
  intro x
  obtain ⟨p, hp, hx⟩ := mem_iUnion₂.mp (hs (mem_univ x))
  refine ⟨fun t => Φ p (x, t), (hcurve p x hx).1,
    (hcurve p x hx).2.mono ?_⟩
  exact Ioo_subset_Ioo (neg_le_neg (hbound p hp)) (hbound p hp)

#print axioms actual_smooth_complex_field_uniform_local_time

theorem actual_smooth_complex_field_is_complete
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E] [CompactSpace E] [T2Space E]
    (X : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (hX : ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (X x))) :
    ∀ x : E, ∃ γ : ℝ → E, γ 0 = x ∧ IsMIntegralCurve γ X := by
  obtain ⟨ε, hε, hlocal⟩ := actual_smooth_complex_field_uniform_local_time X hX
  exact exists_isMIntegralCurve_of_isMIntegralCurveOn
    (hX.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)) hε hlocal

#print axioms actual_smooth_complex_field_is_complete

theorem actual_smooth_complex_field_complete_flow_laws
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E] [CompactSpace E] [T2Space E]
    (X : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (hX : ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (X x))) :
    ∃ Φ : E → ℝ → E,
      (∀ x, Φ x 0 = x) ∧ (∀ x, IsMIntegralCurve (Φ x) X) ∧
      (∀ x s t, Φ x (s + t) = Φ (Φ x s) t) ∧
      (∀ x t, Φ (Φ x t) (-t) = x) ∧
      (∀ t, Bijective (fun x => Φ x t)) ∧
      ∀ x, Continuous (Φ x) := by
  classical
  choose Φ hzero hcurve using actual_smooth_complex_field_is_complete X hX
  have hadd : ∀ x s t, Φ x (s + t) = Φ (Φ x s) t := by
    intro x s t
    have heq := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0)
      (hX.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞))
      ((hcurve x).comp_add s) (hcurve (Φ x s))
      (by simp [hzero])
    simpa [Function.comp_def, add_comm] using congrFun heq t
  have hinv : ∀ x t, Φ (Φ x t) (-t) = x := by
    intro x t
    rw [← hadd, add_neg_cancel, hzero]
  refine ⟨Φ, hzero, hcurve, hadd, hinv, ?_, fun x => (hcurve x).continuous⟩
  intro t
  constructor
  · intro x y hxy
    have hh := congrArg (fun z => Φ z (-t)) hxy
    simpa [hinv] using hh
  · intro x
    exact ⟨Φ x (-t), by simpa using hinv x (-t)⟩

#print axioms actual_smooth_complex_field_complete_flow_laws
