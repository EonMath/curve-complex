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
import CurveComplexGenusTwo.Topology.ActualSimultaneousCriticalWindow.ActualMorseUphillIntegralCurve

open scoped Manifold ContDiff Bundle
open Bundle Set Topology

theorem actual_smooth_supported_division_by_energy
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (b g : E → ℝ)
    (hb : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ b)
    (hg : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ g)
    (hs : tsupport b ⊆ {x : E | g x ≠ 0}) :
    ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ (fun x => b x / g x) := by
  let U : Set E := {x | g x ≠ 0}
  have hU : IsOpen U := by
    simpa [U, Set.compl_setOf] using
      (isClosed_eq hg.continuous continuous_const).isOpen_compl
  have hV : IsOpen (tsupport b)ᶜ := (isClosed_tsupport b).isOpen_compl
  have hunion : U ∪ (tsupport b)ᶜ = Set.univ := by
    ext x
    constructor
    · intro _; trivial
    · intro _
      by_cases hx : x ∈ tsupport b
      · exact Or.inl (hs hx)
      · exact Or.inr hx
  have hdivU : ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ (fun x => b x / g x) U :=
    (hb.contMDiffOn).div₀ hg.contMDiffOn (fun x hx => hx)
  have hzero : EqOn (fun x => b x / g x) (fun _ : E => (0 : ℝ))
      (tsupport b)ᶜ := by
    intro x hx
    have hbzero : b x = 0 := by
      by_contra h
      exact hx (subset_tsupport b h)
    simp [hbzero]
  have hdivV : ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞
      (fun x => b x / g x) (tsupport b)ᶜ := by
    exact contMDiffOn_const.congr hzero
  exact contMDiff_of_contMDiffOn_union_of_isOpen hdivU hdivV hunion hU hV

theorem actual_normalized_integral_curve_height_translation
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (F : E → ℝ) (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F)
    (Y : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (K : Set E)
    (hunit : ∀ x ∈ K,
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F x))
        ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x) (Y x)) = 1)
    (γ : ℝ → E) (a b : ℝ) (hab : a ≤ b)
    (hcurve : ∀ t ∈ Icc a b, IsMIntegralCurveAt γ Y t)
    (hinside : ∀ t ∈ Icc a b, γ t ∈ K) :
    F (γ b) - F (γ a) = b - a := by
  rcases eq_or_lt_of_le hab with rfl | hab'
  · simp
  let g : ℝ → ℝ := F ∘ γ
  have hgcont : ContinuousOn g (Icc a b) := by
    intro t ht
    exact (actual_integral_curve_scalar_height_derivative F hF Y γ t
      (hcurve t ht)).continuousAt.continuousWithinAt
  have hgdiff : DifferentiableOn ℝ g (Ioo a b) := by
    intro t ht
    have ht' : t ∈ Icc a b := Ioo_subset_Icc_self ht
    exact (actual_integral_curve_scalar_height_derivative F hF Y γ t
      (hcurve t ht')).differentiableAt.differentiableWithinAt
  obtain ⟨t, ht, hmean⟩ := exists_deriv_eq_slope g hab' hgcont hgdiff
  have ht' : t ∈ Icc a b := Ioo_subset_Icc_self ht
  have hderiv : deriv g t = 1 := by
    rw [(actual_integral_curve_scalar_height_derivative F hF Y γ t
      (hcurve t ht')).deriv]
    exact hunit (γ t) (hinside t ht')
  rw [hderiv] at hmean
  have hratio := (div_eq_iff (sub_ne_zero.mpr hab'.ne')).mp hmean.symm
  simpa [g] using hratio

