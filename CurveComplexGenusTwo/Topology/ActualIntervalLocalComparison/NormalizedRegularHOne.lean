import CurveComplexGenusTwo.Topology.ActualIntervalLocalComparison.ActualOneFormBridge

open scoped Manifold ContDiff Bundle Simplicial
open CategoryTheory CurveComplexGenusTwo.CWHurewicz
open Convexity
open CanonicalDimensionTwo

namespace CanonicalDimensionTwo

noncomputable def ActualRegularPath.rightHalf {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (γ : ActualRegularPath E) : ActualRegularPath E where
  toFun := fun t => γ.toFun ((1 + t) / 2)
  continuous := γ.continuous.comp (by fun_prop)
  chartDifferentiable := by
    intro t
    simpa only [Function.comp_def] using
      (γ.chartDifferentiable ((1 + t) / 2)).comp t
        (by fun_prop : DifferentiableAt ℝ (fun u : ℝ => (1 + u) / 2) t)
  integrable := by
    intro s
    have hhalf : IntervalIntegrable (actualPathIntegrand s γ.toFun)
        MeasureTheory.volume (1 / 2 : ℝ) 1 :=
      (γ.integrable s).mono_set (by
        rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1),
          Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        exact Set.Icc_subset_Icc (by norm_num) le_rfl)
    have hshift := hhalf.comp_add_right (1 / 2 : ℝ)
    have h := hshift.comp_mul_left (c := (1 / 2 : ℝ))
    have harg (u : ℝ) : (1 + u) / 2 = (1 / 2 : ℝ) * u + 1 / 2 := by
      ring
    have heq : actualPathIntegrand s (fun t => γ.toFun ((1 + t) / 2)) =
        fun t => (1 / 2 : ℝ) • actualPathIntegrand s γ.toFun ((1 + t) / 2) := by
      funext t
      simpa only [harg] using
        actualPathIntegrand_affine s γ.toFun γ.chartDifferentiable
          (1 / 2 : ℝ) (1 / 2 : ℝ) t
    change IntervalIntegrable
      (actualPathIntegrand s (fun t => γ.toFun ((1 + t) / 2)))
      MeasureTheory.volume 0 1
    rw [heq]
    convert h.smul (1 / 2 : ℝ) using 1 <;> norm_num
    funext t
    simp [Pi.smul_apply, RCLike.real_smul_eq_coe_smul (K := ℂ),
      smul_eq_mul, harg, div_eq_mul_inv, mul_comm]

theorem actualRegularSubdivision_boundary_zero {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (γ : ActualRegularPath E) :
    actualRegularChainBoundary
      (Finsupp.single γ 1 - Finsupp.single γ.leftHalf 1 -
        Finsupp.single γ.rightHalf 1) = 0 := by
  rw [map_sub, map_sub, actualRegularChainBoundary_single,
    actualRegularChainBoundary_single, actualRegularChainBoundary_single]
  simp only [ActualRegularPath.leftHalf, ActualRegularPath.rightHalf]
  norm_num

noncomputable def actualRegularReverseCycle {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (γ : ActualRegularPath E) : ActualRegularOneCycles E :=
  ⟨Finsupp.single γ 1 + Finsupp.single γ.reverse 1,
    actualRegularChainBoundary_reverse γ⟩

noncomputable def actualRegularSubdivisionCycle {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (γ : ActualRegularPath E) : ActualRegularOneCycles E :=
  ⟨Finsupp.single γ 1 - Finsupp.single γ.leftHalf 1 -
    Finsupp.single γ.rightHalf 1,
    actualRegularSubdivision_boundary_zero γ⟩

theorem actualRegularSubdivision_period_zero {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (γ : ActualRegularPath E) :
    actualRegularCyclePeriod s (actualRegularSubdivisionCycle γ) = 0 := by
  change actualRegularChainIntegral s
    (Finsupp.single γ 1 - Finsupp.single γ.leftHalf 1 -
      Finsupp.single γ.rightHalf 1) = 0
  rw [map_sub, map_sub, actualRegularChainIntegral_single,
    actualRegularChainIntegral_single, actualRegularChainIntegral_single]
  let f := actualPathIntegrand s γ.toFun
  have hleft : actualPathIntegral s γ.leftHalf.toFun =
      ∫ t in (0 : ℝ)..(1 / 2 : ℝ), f t := by
    change (∫ t in (0 : ℝ)..1,
      actualPathIntegrand s (fun u => γ.toFun (u / 2)) t) = _
    conv_lhs =>
      arg 1
      ext t
      rw [show (fun u => γ.toFun (u / 2)) =
        (fun u => γ.toFun ((1 / 2 : ℝ) * u + 0)) by
          funext u; congr 1; ring]
      rw [actualPathIntegrand_affine s γ.toFun γ.chartDifferentiable
        (1 / 2 : ℝ) 0 t]
    rw [intervalIntegral.integral_smul]
    simpa [f] using
      (intervalIntegral.smul_integral_comp_mul_left
        (a := (0 : ℝ)) (b := 1) f (1 / 2 : ℝ))
  have hright : actualPathIntegral s γ.rightHalf.toFun =
      ∫ t in (1 / 2 : ℝ)..1, f t := by
    change (∫ t in (0 : ℝ)..1,
      actualPathIntegrand s (fun u => γ.toFun ((1 + u) / 2)) t) = _
    conv_lhs =>
      arg 1
      ext t
      rw [show (fun u => γ.toFun ((1 + u) / 2)) =
        (fun u => γ.toFun ((1 / 2 : ℝ) * u + 1 / 2)) by
          funext u; congr 1; ring]
      rw [actualPathIntegrand_affine s γ.toFun γ.chartDifferentiable
        (1 / 2 : ℝ) (1 / 2 : ℝ) t]
    rw [intervalIntegral.integral_smul]
    convert (intervalIntegral.smul_integral_comp_mul_add
      (a := (0 : ℝ)) (b := 1) f (1 / 2 : ℝ) (1 / 2 : ℝ)) using 1 <;> norm_num
  rw [hleft, hright, actualPathIntegral_split s γ.toFun (γ.integrable s)
    (1 / 2 : ℝ) (by norm_num) (by norm_num)]
  abel

def actualNormalizedRelationSet {E : Type} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    Set (ActualRegularOneCycles E) :=
  Set.range (actualRegularChartTwoBoundaryToCycles (E := E)) ∪
  Set.range (actualRegularConstantCycle (E := E)) ∪
  Set.range (actualRegularReverseCycle (E := E)) ∪
  Set.range (actualRegularSubdivisionCycle (E := E))

noncomputable def actualNormalizedRelations {E : Type} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    Submodule ℤ (ActualRegularOneCycles E) :=
  Submodule.span ℤ (actualNormalizedRelationSet (E := E))

abbrev ActualNormalizedRegularHOne (E : Type) [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :=
  ActualRegularOneCycles E ⧸ actualNormalizedRelations (E := E)

noncomputable def actualRegularReversalSimplex {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (γ : ActualRegularPath E) :
    (TopCat.toSSet.obj (TopCat.of E)) _⦋2⦌ :=
  (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋2⦌)).symm
    ⟨fun z => γ.toFun (z.weights 1),
      γ.continuous.comp (StdSimplex.continuous_weights_apply ℝ 1)⟩

theorem actualRegularReversalSimplex_face_two {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (γ : ActualRegularPath E) :
    (TopCat.toSSet.obj (TopCat.of E)).δ (2 : Fin 3)
      (actualRegularReversalSimplex γ) = actualRegularPathAsSingular γ := by
  apply (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌)).injective
  apply ContinuousMap.ext
  intro z
  rw [TopCat.toSSetObjEquiv_δ_apply]
  change γ.toFun ((z.map (2 : Fin 3).succAbove).weights 1) =
    γ.toFun ((TopCat.stdSimplexHomeomorphI.{0} z).down : ℝ)
  congr 1
  change (z.map (2 : Fin 3).succAbove).weights 1 = z.weights 1
  simp [StdSimplex.weights_map, Finsupp.mapDomain, Finsupp.sum_fintype,
    Fin.sum_univ_two, Fin.succAbove]

theorem actualRegularReversalSimplex_face_one {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (γ : ActualRegularPath E) :
    (TopCat.toSSet.obj (TopCat.of E)).δ (1 : Fin 3)
      (actualRegularReversalSimplex γ) =
      actualConstantSingularSimplex E (γ.toFun 0) 1 := by
  apply (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌)).injective
  apply ContinuousMap.ext
  intro z
  rw [TopCat.toSSetObjEquiv_δ_apply]
  change γ.toFun ((z.map (1 : Fin 3).succAbove).weights 1) = γ.toFun 0
  congr 1
  simp [StdSimplex.weights_map, Finsupp.mapDomain, Finsupp.sum_fintype,
    Fin.sum_univ_two]

theorem actualRegularReversalSimplex_face_zero {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (γ : ActualRegularPath E) :
    (TopCat.toSSet.obj (TopCat.of E)).δ (0 : Fin 3)
      (actualRegularReversalSimplex γ) =
      actualRegularPathAsSingular γ.reverse := by
  apply (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌)).injective
  apply ContinuousMap.ext
  intro z
  rw [TopCat.toSSetObjEquiv_δ_apply]
  change γ.toFun ((z.map (0 : Fin 3).succAbove).weights 1) =
    γ.toFun (1 - (TopCat.stdSimplexHomeomorphI.{0} z).down)
  congr 1
  change (z.map (0 : Fin 3).succAbove).weights 1 = 1 - z.weights 1
  have ht := z.total
  rw [Finsupp.sum_fintype] at ht <;> try simp
  change (∑ j : Fin 2, z.weights j) = 1 at ht
  rw [Fin.sum_univ_two] at ht
  simp [StdSimplex.weights_map, Finsupp.mapDomain, Finsupp.sum_fintype,
    Fin.sum_univ_two]
  linarith

noncomputable def actualRegularReversalFiller {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (γ : ActualRegularPath E) :
    (TopCat.toSSet.obj (TopCat.of E)) _⦋2⦌ →₀ ℤ :=
  Finsupp.single (actualRegularReversalSimplex γ) 1 +
    Finsupp.single (actualConstantSingularSimplex E (γ.toFun 0) 2) 1

theorem actualRegularReversalFiller_boundary {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (γ : ActualRegularPath E) :
    singularBoundaryFinsupp (TopCat.of E) 1
      (actualRegularReversalFiller γ) =
      Finsupp.single (actualRegularPathAsSingular γ) 1 +
        Finsupp.single (actualRegularPathAsSingular γ.reverse) 1 := by
  rw [actualRegularReversalFiller, map_add, singularBoundaryFinsupp_single,
    actualConstantSingularSimplex_bounds]
  simp [Fin.sum_univ_succ, actualRegularReversalSimplex_face_zero,
    actualRegularReversalSimplex_face_one,
    actualRegularReversalSimplex_face_two]
  abel

theorem actualRegularReverseCycle_singular_boundary {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (γ : ActualRegularPath E) :
    actualRegularCyclesToSingular (actualRegularReverseCycle γ) ∈
      actualSingularTwoBoundaries E := by
  refine ⟨actualRegularReversalFiller γ, ?_⟩
  apply Subtype.ext
  change singularBoundaryFinsupp (TopCat.of E) 1
      (actualRegularReversalFiller γ) =
    actualRegularChainsToSingular
      (Finsupp.single γ 1 + Finsupp.single γ.reverse 1)
  rw [actualRegularReversalFiller_boundary, map_add]
  simp [actualRegularChainsToSingular, Finsupp.lmapDomain_apply]

noncomputable def actualRegularSubdivisionSimplex {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (γ : ActualRegularPath E) :
    (TopCat.toSSet.obj (TopCat.of E)) _⦋2⦌ :=
  (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋2⦌)).symm
    ⟨fun z => γ.toFun (z.weights 1 / 2 + z.weights 2),
      γ.continuous.comp
        (((StdSimplex.continuous_weights_apply ℝ (1 : Fin 3)).div_const 2).add
          (StdSimplex.continuous_weights_apply ℝ (2 : Fin 3)))⟩

theorem actualRegularSubdivisionSimplex_face_two {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (γ : ActualRegularPath E) :
    (TopCat.toSSet.obj (TopCat.of E)).δ (2 : Fin 3)
      (actualRegularSubdivisionSimplex γ) =
      actualRegularPathAsSingular γ.leftHalf := by
  apply (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌)).injective
  apply ContinuousMap.ext
  intro z
  rw [TopCat.toSSetObjEquiv_δ_apply]
  change γ.toFun (((z.map (2 : Fin 3).succAbove).weights 1) / 2 +
    (z.map (2 : Fin 3).succAbove).weights 2) =
    γ.toFun (((TopCat.stdSimplexHomeomorphI.{0} z).down : ℝ) / 2)
  congr 1
  change ((z.map (2 : Fin 3).succAbove).weights 1) / 2 +
    (z.map (2 : Fin 3).succAbove).weights 2 = z.weights 1 / 2
  simp [StdSimplex.weights_map, Finsupp.mapDomain, Finsupp.sum_fintype,
    Fin.sum_univ_two, Fin.succAbove]

theorem actualRegularSubdivisionSimplex_face_one {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (γ : ActualRegularPath E) :
    (TopCat.toSSet.obj (TopCat.of E)).δ (1 : Fin 3)
      (actualRegularSubdivisionSimplex γ) =
      actualRegularPathAsSingular γ := by
  apply (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌)).injective
  apply ContinuousMap.ext
  intro z
  rw [TopCat.toSSetObjEquiv_δ_apply]
  change γ.toFun (((z.map (1 : Fin 3).succAbove).weights 1) / 2 +
    (z.map (1 : Fin 3).succAbove).weights 2) =
    γ.toFun ((TopCat.stdSimplexHomeomorphI.{0} z).down : ℝ)
  congr 1
  change ((z.map (1 : Fin 3).succAbove).weights 1) / 2 +
    (z.map (1 : Fin 3).succAbove).weights 2 = z.weights 1
  simp [StdSimplex.weights_map, Finsupp.mapDomain, Finsupp.sum_fintype,
    Fin.sum_univ_two, Fin.succAbove]

theorem actualRegularSubdivisionSimplex_face_zero {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (γ : ActualRegularPath E) :
    (TopCat.toSSet.obj (TopCat.of E)).δ (0 : Fin 3)
      (actualRegularSubdivisionSimplex γ) =
      actualRegularPathAsSingular γ.rightHalf := by
  apply (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌)).injective
  apply ContinuousMap.ext
  intro z
  rw [TopCat.toSSetObjEquiv_δ_apply]
  change γ.toFun (((z.map (0 : Fin 3).succAbove).weights 1) / 2 +
    (z.map (0 : Fin 3).succAbove).weights 2) =
    γ.toFun ((1 + (TopCat.stdSimplexHomeomorphI.{0} z).down) / 2)
  congr 1
  change ((z.map (0 : Fin 3).succAbove).weights 1) / 2 +
    (z.map (0 : Fin 3).succAbove).weights 2 = (1 + z.weights 1) / 2
  have ht := z.total
  rw [Finsupp.sum_fintype] at ht <;> try simp
  change (∑ j : Fin 2, z.weights j) = 1 at ht
  rw [Fin.sum_univ_two] at ht
  simp [StdSimplex.weights_map, Finsupp.mapDomain, Finsupp.sum_fintype,
    Fin.sum_univ_two, Fin.succAbove]
  linarith

theorem actualRegularSubdivisionSimplex_boundary {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (γ : ActualRegularPath E) :
    singularBoundaryFinsupp (TopCat.of E) 1
      (Finsupp.single (actualRegularSubdivisionSimplex γ) (-1)) =
      Finsupp.single (actualRegularPathAsSingular γ) 1 -
        Finsupp.single (actualRegularPathAsSingular γ.leftHalf) 1 -
        Finsupp.single (actualRegularPathAsSingular γ.rightHalf) 1 := by
  rw [show Finsupp.single (actualRegularSubdivisionSimplex γ) (-1 : ℤ) =
      -Finsupp.single (actualRegularSubdivisionSimplex γ) 1 by simp,
    map_neg, singularBoundaryFinsupp_single]
  simp [Fin.sum_univ_succ, actualRegularSubdivisionSimplex_face_zero,
    actualRegularSubdivisionSimplex_face_one,
    actualRegularSubdivisionSimplex_face_two]
  abel

theorem actualRegularSubdivisionCycle_singular_boundary {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (γ : ActualRegularPath E) :
    actualRegularCyclesToSingular (actualRegularSubdivisionCycle γ) ∈
      actualSingularTwoBoundaries E := by
  refine ⟨Finsupp.single (actualRegularSubdivisionSimplex γ) (-1), ?_⟩
  apply Subtype.ext
  change singularBoundaryFinsupp (TopCat.of E) 1
      (Finsupp.single (actualRegularSubdivisionSimplex γ) (-1)) =
    actualRegularChainsToSingular
      (Finsupp.single γ 1 - Finsupp.single γ.leftHalf 1 -
        Finsupp.single γ.rightHalf 1)
  rw [actualRegularSubdivisionSimplex_boundary, map_sub, map_sub]
  simp [actualRegularChainsToSingular, Finsupp.lmapDomain_apply]

end CanonicalDimensionTwo
