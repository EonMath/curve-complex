import CurveComplexGenusTwo.Topology.ActualIntervalLocalComparison.IntervalLocalKernel
import CurveComplexGenusTwo.Topology.ActualCanonicalDimensionTwo.GenusTwoIntegralH1
import CurveComplexGenusTwo.Topology.ActualCanonicalDimensionTwo.ActualOneFormBridgePeriodInjectiveTailCanonical85

open scoped Manifold ContDiff Bundle Simplicial TensorProduct
open CategoryTheory CurveComplexGenusTwo.CWHurewicz
open CanonicalDimensionTwo

namespace CanonicalDimensionTwo

set_option maxHeartbeats 1000000

noncomputable def intervalLocalHOneProjectEquiv {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    IntervalLocalNormalizedRegularHOne E ≃ₗ[ℤ]
      CurveComplex.integralHomology E 1 :=
  LinearEquiv.ofBijective intervalLocalNormalizedRegularHOneToProject
    intervalLocalNormalizedRegularHOneToProject_bijective

noncomputable def actualSectionPeriodOnProject {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) :
    CurveComplex.integralHomology E 1 →ₗ[ℤ] ℂ :=
  (intervalLocalNormalizedRegularPeriod s).comp
    (intervalLocalHOneProjectEquiv (E := E)).symm.toLinearMap

theorem actualSectionPeriodOnProject_mk {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (z : ActualRegularOneCycles E) :
    actualSectionPeriodOnProject s
      (intervalLocalNormalizedRegularHOneToProject
        ((intervalLocalNormalizedRelations (E := E)).mkQ z)) =
      actualRegularCyclePeriod s z := by
  simp [actualSectionPeriodOnProject, intervalLocalHOneProjectEquiv]
  exact intervalLocalNormalizedRegularPeriod_mk s z

noncomputable def actualSectionPeriodOnProjectLinear {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    ActualCanonicalSection E →ₗ[ℂ]
      (CurveComplex.integralHomology E 1 →ₗ[ℤ] ℂ) where
  toFun := actualSectionPeriodOnProject
  map_add' s t := by
    apply LinearMap.ext
    intro x
    obtain ⟨q, rfl⟩ :=
      intervalLocalNormalizedRegularHOneToProject_surjective x
    obtain ⟨z, rfl⟩ :=
      (intervalLocalNormalizedRelations (E := E)).mkQ_surjective q
    simp only [LinearMap.add_apply, actualSectionPeriodOnProject_mk]
    change actualRegularChainIntegral (s + t) z.1 =
      actualRegularChainIntegral s z.1 + actualRegularChainIntegral t z.1
    rw [actualRegularChainIntegral_add]
    rfl
  map_smul' c s := by
    apply LinearMap.ext
    intro x
    obtain ⟨q, rfl⟩ :=
      intervalLocalNormalizedRegularHOneToProject_surjective x
    obtain ⟨z, rfl⟩ :=
      (intervalLocalNormalizedRelations (E := E)).mkQ_surjective q
    simp only [LinearMap.smul_apply, actualSectionPeriodOnProject_mk]
    change actualRegularChainIntegral (c • s) z.1 =
      c • actualRegularChainIntegral s z.1
    rw [actualRegularChainIntegral_smul]
    rfl

noncomputable def actualPeriodToDual (E : Type) [TopologicalSpace E] :
    (CurveComplex.integralHomology E 1 →ₗ[ℤ] ℂ) →ₗ[ℂ]
      Module.Dual ℂ (ℂ ⊗[ℤ] CurveComplex.integralHomology E 1) :=
  (TensorProduct.AlgebraTensorModule.lift.equiv ℤ ℂ ℂ ℂ
    (CurveComplex.integralHomology E 1) ℂ).toLinearMap.comp
    (LinearMap.lsmul ℂ (CurveComplex.integralHomology E 1 →ₗ[ℤ] ℂ)).flip

noncomputable def actualSectionPeriodDual {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    ActualCanonicalSection E →ₗ[ℂ]
      Module.Dual ℂ (ℂ ⊗[ℤ] CurveComplex.integralHomology E 1) :=
  (actualPeriodToDual E).comp actualSectionPeriodOnProjectLinear

theorem actualSectionPeriodDual_tmul {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (c : ℂ)
    (x : CurveComplex.integralHomology E 1) :
    (actualSectionPeriodDual s) (c ⊗ₜ[ℤ] x) =
      c * actualSectionPeriodOnProject s x := by
  change (TensorProduct.AlgebraTensorModule.lift
      ((LinearMap.lsmul ℂ
        (CurveComplex.integralHomology E 1 →ₗ[ℤ] ℂ)).flip
        (actualSectionPeriodOnProjectLinear s))) (c ⊗ₜ[ℤ] x) = _
  rw [TensorProduct.AlgebraTensorModule.lift_tmul]
  change (c • actualSectionPeriodOnProject s) x = _
  simp [smul_eq_mul]

theorem actualSectionPeriodDual_injective
    (E : Type) [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (hg : CurveComplex.IsGenus E 2)
    (A : ChartedSpace ℂ E)
    (hA : letI : ChartedSpace ℂ E := A;
      IsManifold 𝓘(ℂ) ∞ E) :
    letI : ChartedSpace ℂ E := A
    letI : IsManifold 𝓘(ℂ) ∞ E := hA
    Function.Injective (actualSectionPeriodDual (E := E)) := by
  letI : ChartedSpace ℂ E := A
  letI : IsManifold 𝓘(ℂ) ∞ E := hA
  apply LinearMap.ker_eq_bot.mp
  rw [eq_bot_iff]
  intro s hs
  rw [LinearMap.mem_ker] at hs
  have hperiod : ∀ z : ActualRegularOneCycles E,
      actualRegularCyclePeriod s z = 0 := by
    intro z
    have ht := congrArg (fun f : Module.Dual ℂ
        (ℂ ⊗[ℤ] CurveComplex.integralHomology E 1) =>
      f (1 ⊗ₜ[ℤ] (intervalLocalNormalizedRegularHOneToProject
        ((intervalLocalNormalizedRelations (E := E)).mkQ z)))) hs
    rw [actualSectionPeriodDual_tmul, one_mul] at ht
    rw [actualSectionPeriodOnProject_mk] at ht
    simpa using ht
  have hinj := actualRegularCyclePeriod_injective E hg A hA
  have hzero : actualRegularCyclePeriod (0 : ActualCanonicalSection E) = 0 := by
    apply LinearMap.ext
    intro z
    have h := congrArg (fun p : ActualRegularOneChains E →ₗ[ℤ] ℂ => p z.1)
      (map_zero (actualRegularPeriod (E := E)))
    simpa [actualRegularPeriod, actualRegularCyclePeriod] using h
  have hs0 : s = 0 := hinj (by
    change actualRegularCyclePeriod s = actualRegularCyclePeriod 0
    rw [hzero]
    apply LinearMap.ext
    exact hperiod)
  exact hs0 ▸ Submodule.zero_mem _

theorem actualCanonicalSection_finrank_le_four
    (E : Type) [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (hg : CurveComplex.IsGenus E 2)
    (A : ChartedSpace ℂ E)
    (hA : letI : ChartedSpace ℂ E := A;
      IsManifold 𝓘(ℂ) ∞ E) :
    letI : ChartedSpace ℂ E := A
    letI : IsManifold 𝓘(ℂ) ∞ E := hA
    Module.finrank ℂ (ActualCanonicalSection E) ≤ 4 := by
  letI : ChartedSpace ℂ E := A
  letI : IsManifold 𝓘(ℂ) ∞ E := hA
  letI : Module.Finite ℂ
      (Module.Dual ℂ (ℂ ⊗[ℤ] CurveComplex.integralHomology E 1)) :=
    Module.Finite.of_basis (genus_two_complex_h1_dual_basis E hg)
  have h := LinearMap.finrank_le_finrank_of_injective
    (actualSectionPeriodDual_injective E hg A hA)
  rw [genus_two_complex_h1_dual_finrank_four E hg] at h
  exact h

end CanonicalDimensionTwo
