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

set_option backward.isDefEq.respectTransparency false

namespace CurveComplexGenusTwo.CWHurewicz
open CategoryTheory
open scoped Simplicial

private theorem actual_projection_zero_iff
    (X : TopCat) (A : Set X) (i : ℕ)
    (c : (TopCat.toSSet.obj X) _⦋i⦌ →₀ ℤ) :
    canonicalRelativeProjection X A i c = 0 ↔ c ∈ excisionSubspaceChains X A i := by
  change c ∈ LinearMap.ker (canonicalRelativeProjection X A i) ↔ _
  rw [canonicalRelativeProjection_kernel]

private theorem actual_small_chain_split
    (X : TopCat) (A U : Set X) (i : ℕ)
    (c : (TopCat.toSSet.obj X) _⦋i⦌ →₀ ℤ)
    (hc : c ∈ smallSingularChains X A U i) :
    ∃ d : (TopCat.toSSet.obj (TopCat.of (Excised X U))) _⦋i⦌ →₀ ℤ,
      c - excisedChainPush X U i d ∈ excisionSubspaceChains X A i := by
  rw [smallSingularChains_eq_sup] at hc
  obtain ⟨v, hv, a, ha, heq⟩ := Submodule.mem_sup.mp hc
  rw [← excisedChainPush_range] at hv
  obtain ⟨d, rfl⟩ := hv
  refine ⟨d, ?_⟩
  have h : c - excisedChainPush X U i d = a := by rw [← heq]; abel
  rw [h]
  exact ha

/-- Subdividing a one-chain gives a small filling with its literal zero-chain
boundary unchanged. Thus no missing negative-degree cycle condition occurs. -/
theorem actual_relative_zero_chain_has_small_filling
    (X : TopCat) (A U : Set X) (hU : closure U ⊆ interior A)
    (z : (TopCat.toSSet.obj X) _⦋0⦌ →₀ ℤ)
    (b : (TopCat.toSSet.obj X) _⦋1⦌ →₀ ℤ)
    (hb : SingularChainImageSupported X 0 A (z - singularBoundaryFinsupp X 0 b)) :
    ∃ b' : (TopCat.toSSet.obj X) _⦋1⦌ →₀ ℤ,
      b' ∈ smallSingularChains X A U 1 ∧
      SingularChainImageSupported X 0 A (z - singularBoundaryFinsupp X 0 b') := by
  obtain ⟨k, hk⟩ := singularBarycentricIterate_eventually_small_submodule X A U hU 1 b
  refine ⟨singularBarycentricIterate X 1 k b, hk, ?_⟩
  rw [singularBarycentricIterate_boundary X 0 k b,
    singularBarycentricIterate_degree_zero]
  exact hb

theorem actual_excision_zero_chain_reflects_boundary
    (X : Type) [TopologicalSpace X] (A U : Set X)
    (hU : closure U ⊆ interior A)
    (x : (relativeSingularChains (Excised X U) (excisedSubspace A U)).X 0)
    (b : (relativeSingularChains X A).X 1)
    (hb : (excisionRelativeChainMap A U).f 0 x = (relativeSingularChains X A).d 1 0 b) :
    ∃ d : (relativeSingularChains (Excised X U) (excisedSubspace A U)).X 1,
      (relativeSingularChains (Excised X U) (excisedSubspace A U)).d 1 0 d = x := by
  let Y := TopCat.of (Excised X U)
  let B := excisedSubspace A U
  obtain ⟨c, rfl⟩ := canonicalRelativeProjection_surjective Y B 0 x
  obtain ⟨a, rfl⟩ := canonicalRelativeProjection_surjective (TopCat.of X) A 1 b
  rw [canonicalRelativeProjection_excision (TopCat.of X) A U 0,
    canonicalRelativeProjection_boundary (TopCat.of X) A 0] at hb
  have hres := (actual_projection_zero_iff (TopCat.of X) A 0
    (excisedChainPush (TopCat.of X) U 0 c - singularBoundaryFinsupp (TopCat.of X) 0 a)).mp
      (by rw [map_sub, hb, sub_self])
  obtain ⟨a', ha', he⟩ := actual_relative_zero_chain_has_small_filling
    (TopCat.of X) A U hU _ a (fun s hs => hres hs)
  obtain ⟨d, hd⟩ := actual_small_chain_split (TopCat.of X) A U 1 a' ha'
  have hp : canonicalRelativeProjection (TopCat.of X) A 1 a' =
      canonicalRelativeProjection (TopCat.of X) A 1 (excisedChainPush (TopCat.of X) U 1 d) := by
    simpa only [map_sub, sub_eq_zero] using
      (actual_projection_zero_iff (TopCat.of X) A 1 _).mpr hd
  refine ⟨canonicalRelativeProjection Y B 1 d, ?_⟩
  rw [canonicalRelativeProjection_boundary Y B 0]
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (actual_projection_zero_iff Y B 0 _).mpr
  apply (excisedChainPush_subspace_iff (TopCat.of X) A U 0 _).mp
  apply (actual_projection_zero_iff (TopCat.of X) A 0 _).mp
  rw [map_sub, ← excisedChainPush_boundary, map_sub]
  have hr := (actual_projection_zero_iff (TopCat.of X) A 0 _).mpr
    (show _ ∈ excisionSubspaceChains (TopCat.of X) A 0 from fun s hs => he s hs)
  rw [map_sub, sub_eq_zero] at hr
  rw [← canonicalRelativeProjection_boundary (TopCat.of X) A 0, ← hp,
    canonicalRelativeProjection_boundary (TopCat.of X) A 0, ← hr]
  exact sub_self _

/-- The genuine canonical singular excision inclusion is an isomorphism also
in degree zero. The boundary reflection is proved, not assumed. -/
theorem actual_canonicalExcisionHomologyMap_zero_isIso
    (X : Type) [TopologicalSpace X] (A U : Set X)
    (hU : closure U ⊆ interior A) :
    IsIso (HomologicalComplex.homologyMap (excisionRelativeChainMap A U) 0) := by
  let Y := TopCat.of (Excised X U)
  let B := excisedSubspace A U
  let K := relativeSingularChains (Excised X U) B
  let L := relativeSingularChains X A
  let f := excisionRelativeChainMap A U
  have chainSurj (y : L.X 0) : ∃ x : K.X 0, f.f 0 x = y := by
    obtain ⟨c, rfl⟩ := canonicalRelativeProjection_surjective (TopCat.of X) A 0 y
    obtain ⟨k, hk⟩ := singularBarycentricIterate_eventually_small_submodule
      (TopCat.of X) A U hU 0 c
    rw [singularBarycentricIterate_degree_zero] at hk
    obtain ⟨d, hd⟩ := actual_small_chain_split (TopCat.of X) A U 0 c hk
    refine ⟨canonicalRelativeProjection Y B 0 d, ?_⟩
    dsimp only [f, Y, B]
    rw [canonicalRelativeProjection_excision (TopCat.of X) A U 0]
    have hh := (actual_projection_zero_iff (TopCat.of X) A 0 _).mpr hd
    rw [map_sub, sub_eq_zero] at hh
    exact hh.symm
  have classEq (M : ChainComplex (ModuleCat.{0} ℤ) ℕ) (z w : M.cycles 0) :
      M.homologyπ 0 z = M.homologyπ 0 w ↔
      ∃ b : M.X 1, M.d 1 0 b = M.iCycles 0 z - M.iCycles 0 w := by
    rw [← (ModuleCat.mono_iff_injective (M.homologyι 0)).mp inferInstance |>.eq_iff]
    change (M.homologyπ 0 ≫ M.homologyι 0) z =
      (M.homologyπ 0 ≫ M.homologyι 0) w ↔ _
    rw [M.homology_π_ι 0]
    have h := (M.sc 0).moduleCat_pOpcycles_eq_iff (M.iCycles 0 z) (M.iCycles 0 w)
    change _ ↔ ∃ b : M.X ((ComplexShape.down ℕ).prev 0),
      M.d _ 0 b = M.iCycles 0 z - M.iCycles 0 w at h
    rw [(ComplexShape.down ℕ).prev_eq' (show (ComplexShape.down ℕ).Rel 1 0 from rfl)] at h
    exact h
  have homSurj : Function.Surjective (HomologicalComplex.homologyMap f 0) := by
    intro y
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (L.homologyπ 0)).mp inferInstance y
    obtain ⟨x, hx⟩ := chainSurj (L.iCycles 0 z)
    obtain ⟨w, hw⟩ := (ModuleCat.epi_iff_surjective (K.iCycles 0)).mp inferInstance x
    refine ⟨K.homologyπ 0 w, ?_⟩
    change (K.homologyπ 0 ≫ HomologicalComplex.homologyMap f 0) w = _
    rw [HomologicalComplex.homologyπ_naturality]
    apply congrArg (fun q => L.homologyπ 0 q)
    apply (ModuleCat.mono_iff_injective (L.iCycles 0)).mp inferInstance
    have hh := congrArg (fun q => q w) (HomologicalComplex.cyclesMap_i f 0)
    change L.iCycles 0 (HomologicalComplex.cyclesMap f 0 w) = f.f 0 (K.iCycles 0 w) at hh
    erw [hh, hw]
    exact hx
  have homInj : Function.Injective (HomologicalComplex.homologyMap f 0) := by
    intro a a' he
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ 0)).mp inferInstance a
    obtain ⟨w, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ 0)).mp inferInstance a'
    change (K.homologyπ 0 ≫ HomologicalComplex.homologyMap f 0) z =
      (K.homologyπ 0 ≫ HomologicalComplex.homologyMap f 0) w at he
    rw [HomologicalComplex.homologyπ_naturality] at he
    obtain ⟨b, hb⟩ := (classEq L _ _).mp he
    have hz := congrArg (fun q => q z) (HomologicalComplex.cyclesMap_i f 0)
    have hw := congrArg (fun q => q w) (HomologicalComplex.cyclesMap_i f 0)
    change L.iCycles 0 (HomologicalComplex.cyclesMap f 0 z) = f.f 0 (K.iCycles 0 z) at hz
    change L.iCycles 0 (HomologicalComplex.cyclesMap f 0 w) = f.f 0 (K.iCycles 0 w) at hw
    erw [hz, hw, ← map_sub] at hb
    apply (classEq K z w).mpr
    exact actual_excision_zero_chain_reflects_boundary X A U hU _ b hb.symm
  have : Epi (HomologicalComplex.homologyMap f 0) := (ModuleCat.epi_iff_surjective _).mpr homSurj
  have : Mono (HomologicalComplex.homologyMap f 0) := (ModuleCat.mono_iff_injective _).mpr homInj
  exact CategoryTheory.isIso_of_mono_of_epi _

/-- Canonical singular excision in EVERY natural degree. -/
theorem actual_canonicalExcisionHomologyMap_isIso
    (X : Type) [TopologicalSpace X] (A U : Set X)
    (hU : closure U ⊆ interior A) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (excisionRelativeChainMap A U) n) := by
  cases n with
  | zero => exact actual_canonicalExcisionHomologyMap_zero_isIso X A U hU
  | succ n => exact canonicalExcisionHomologyMap_isIso X A U hU n

#print axioms actual_relative_zero_chain_has_small_filling
#print axioms actual_excision_zero_chain_reflects_boundary
#print axioms actual_canonicalExcisionHomologyMap_zero_isIso
#print axioms actual_canonicalExcisionHomologyMap_isIso
end CurveComplexGenusTwo.CWHurewicz
