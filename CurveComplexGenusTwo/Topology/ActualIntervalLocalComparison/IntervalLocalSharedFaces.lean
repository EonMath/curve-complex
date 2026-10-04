import CurveComplexGenusTwo.Topology.ActualIntervalLocalComparison.IntervalLocalFaceCoherence

open scoped Manifold ContDiff Bundle Simplicial
open Convexity CategoryTheory CurveComplexGenusTwo.CWHurewicz
open CanonicalDimensionTwo

namespace CanonicalDimensionTwo

abbrev ActualSingularTwoChains (E : Type) [TopologicalSpace E] :=
  (TopCat.toSSet.obj (TopCat.of E)) _⦋2⦌ →₀ ℤ

abbrev ActualSingularOneChains (E : Type) [TopologicalSpace E] :=
  (TopCat.toSSet.obj (TopCat.of E)) _⦋1⦌ →₀ ℤ

noncomputable def actualFaceSet {E : Type} [TopologicalSpace E]
    (b : ActualSingularTwoChains E) :
    Finset ((TopCat.toSSet.obj (TopCat.of E)) _⦋1⦌) := by
  classical
  exact b.support.biUnion (fun σ =>
    (singularBoundaryFinsupp (TopCat.of E) 1 (Finsupp.single σ 1)).support)

def actualIncidentOpen {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    (b : ActualSingularTwoChains E)
    (i : b.support → ActualChartBallIndex E)
    (y : (TopCat.toSSet.obj (TopCat.of E)) _⦋1⦌) : Set E := by
  classical
  exact ⋂ τ : b.support,
    if y ∈ (singularBoundaryFinsupp (TopCat.of E) 1
        (Finsupp.single τ.1 1)).support
    then actualChartBallCover (i τ)
    else Set.univ

theorem actualIncidentOpen_isOpen {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E]
    (b : ActualSingularTwoChains E)
    (i : b.support → ActualChartBallIndex E)
    (y : (TopCat.toSSet.obj (TopCat.of E)) _⦋1⦌) :
    IsOpen (actualIncidentOpen b i y) := by
  classical
  apply isOpen_iInter_of_finite
  intro τ
  change IsOpen (if y ∈ (singularBoundaryFinsupp (TopCat.of E) 1
      (Finsupp.single τ.1 1)).support
    then actualChartBallCover (i τ) else Set.univ)
  split_ifs
  · exact actualChartBallCover_isOpen (i τ)
  · exact isOpen_univ

theorem actualIncidentOpen_subset_ball {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E]
    (b : ActualSingularTwoChains E)
    (i : b.support → ActualChartBallIndex E)
    (τ : b.support)
    (y : (TopCat.toSSet.obj (TopCat.of E)) _⦋1⦌)
    (hy : y ∈ (singularBoundaryFinsupp (TopCat.of E) 1
      (Finsupp.single τ.1 1)).support) :
    actualIncidentOpen b i y ⊆ actualChartBallCover (i τ) := by
  classical
  intro x hx
  have hτ := Set.mem_iInter.mp (show x ∈ ⋂ ρ : b.support,
      if y ∈ (singularBoundaryFinsupp (TopCat.of E) 1
        (Finsupp.single ρ.1 1)).support
      then actualChartBallCover (i ρ) else Set.univ from hx) τ
  simpa [hy] using hτ

theorem actualFace_image_in_incidentOpen {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E]
    (b : ActualSingularTwoChains E)
    (i : b.support → ActualChartBallIndex E)
    (hsmall : ∀ τ : b.support, ∀ u : StdSimplex ℝ (Fin 3),
      (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋2⦌) τ.1) u ∈
        actualChartBallCover (i τ))
    (y : (TopCat.toSSet.obj (TopCat.of E)) _⦋1⦌)
    (hy : y ∈ actualFaceSet b) :
    ∀ u : StdSimplex ℝ (Fin 2),
      (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌) y) u ∈
        actualIncidentOpen b i y := by
  intro u
  classical
  apply Set.mem_iInter.mpr
  intro τ
  change (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌) y) u ∈
    (if y ∈ (singularBoundaryFinsupp (TopCat.of E) 1
      (Finsupp.single τ.1 1)).support
    then actualChartBallCover (i τ) else Set.univ)
  split_ifs with hface
  · exact actualSingularTriangle_boundary_image_subset τ.1
      (actualChartBallCover (i τ)) (hsmall τ) y hface u
  · exact Set.mem_univ _

structure ActualSharedEdgeReplacement {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (U : Set E) (y : (TopCat.toSSet.obj (TopCat.of E)) _⦋1⦌) where
  regular : ActualRegularOneChains E
  support : ∀ γ ∈ regular.support, ∀ t : ℝ, γ.toFun t ∈ U
  correction : ActualSingularTwoChains E
  correction_boundary :
    singularBoundaryFinsupp (TopCat.of E) 1 correction =
      Finsupp.single y 1 - actualRegularChainsToSingular regular

noncomputable def actualChooseSharedEdge {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (b : ActualSingularTwoChains E)
    (i : b.support → ActualChartBallIndex E)
    (hsmall : ∀ τ : b.support, ∀ u : StdSimplex ℝ (Fin 3),
      (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋2⦌) τ.1) u ∈
        actualChartBallCover (i τ))
    (y : actualFaceSet b) :
    ActualSharedEdgeReplacement (actualIncidentOpen b i y.1) y.1 :=
  Classical.choice (by
    obtain ⟨a, ha, c, hc⟩ := actualSingularEdge_regularize_in_open
      (actualIncidentOpen b i y.1)
      (actualIncidentOpen_isOpen b i y.1) y.1
      (actualFace_image_in_incidentOpen b i hsmall y.1 y.2)
    exact ⟨⟨a, ha, c, hc⟩⟩)

noncomputable def actualSharedEdgeRegular {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (b : ActualSingularTwoChains E)
    (i : b.support → ActualChartBallIndex E)
    (hsmall : ∀ τ : b.support, ∀ u : StdSimplex ℝ (Fin 3),
      (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋2⦌) τ.1) u ∈
        actualChartBallCover (i τ)) :
    ActualSingularOneChains E →ₗ[ℤ] ActualRegularOneChains E := by
  classical
  exact Finsupp.linearCombination ℤ (fun y =>
    if hy : y ∈ actualFaceSet b then
      (actualChooseSharedEdge b i hsmall ⟨y, hy⟩).regular
    else 0)

noncomputable def actualSharedEdgeCorrection {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (b : ActualSingularTwoChains E)
    (i : b.support → ActualChartBallIndex E)
    (hsmall : ∀ τ : b.support, ∀ u : StdSimplex ℝ (Fin 3),
      (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋2⦌) τ.1) u ∈
        actualChartBallCover (i τ)) :
    ActualSingularOneChains E →ₗ[ℤ] ActualSingularTwoChains E := by
  classical
  exact Finsupp.linearCombination ℤ (fun y =>
    if hy : y ∈ actualFaceSet b then
      (actualChooseSharedEdge b i hsmall ⟨y, hy⟩).correction
    else 0)

theorem actualSharedEdgeCorrection_single {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (b : ActualSingularTwoChains E)
    (i : b.support → ActualChartBallIndex E)
    (hsmall : ∀ τ : b.support, ∀ u : StdSimplex ℝ (Fin 3),
      (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋2⦌) τ.1) u ∈
        actualChartBallCover (i τ))
    (y : (TopCat.toSSet.obj (TopCat.of E)) _⦋1⦌)
    (hy : y ∈ actualFaceSet b) :
    singularBoundaryFinsupp (TopCat.of E) 1
        (actualSharedEdgeCorrection b i hsmall (Finsupp.single y 1)) =
      Finsupp.single y 1 - actualRegularChainsToSingular
        (actualSharedEdgeRegular b i hsmall (Finsupp.single y 1)) := by
  classical
  simp only [actualSharedEdgeCorrection, actualSharedEdgeRegular,
    Finsupp.linearCombination_single, one_smul]
  simp only [dif_pos hy]
  exact (actualChooseSharedEdge b i hsmall ⟨y, hy⟩).correction_boundary

theorem actualSharedEdgeCorrection_supported {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (b : ActualSingularTwoChains E)
    (i : b.support → ActualChartBallIndex E)
    (hsmall : ∀ τ : b.support, ∀ u : StdSimplex ℝ (Fin 3),
      (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋2⦌) τ.1) u ∈
        actualChartBallCover (i τ))
    (d : ActualSingularOneChains E)
    (hd : ∀ y ∈ d.support, y ∈ actualFaceSet b) :
    singularBoundaryFinsupp (TopCat.of E) 1
        (actualSharedEdgeCorrection b i hsmall d) =
      d - actualRegularChainsToSingular (actualSharedEdgeRegular b i hsmall d) := by
  classical
  have hrepr : d = ∑ y ∈ d.support, d y • Finsupp.single y 1 := by
    conv_lhs => rw [← Finsupp.sum_single d]
    simp [Finsupp.sum, Finsupp.smul_single]
  conv_lhs => rw [hrepr]
  conv_rhs => rw [hrepr]
  simp only [map_sum, map_smul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  rw [actualSharedEdgeCorrection_single b i hsmall y (hd y hy)]
  rw [smul_sub]

theorem actualTriangleFace_mem_faceSet {E : Type}
    [TopologicalSpace E]
    (b : ActualSingularTwoChains E)
    (τ : b.support)
    (y : (TopCat.toSSet.obj (TopCat.of E)) _⦋1⦌)
    (hy : y ∈ (singularBoundaryFinsupp (TopCat.of E) 1
      (Finsupp.single τ.1 1)).support) :
    y ∈ actualFaceSet b := by
  classical
  exact Finset.mem_biUnion.mpr ⟨τ.1, τ.2, hy⟩

theorem actualSharedEdgeRegular_single_support_in_ball {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (b : ActualSingularTwoChains E)
    (i : b.support → ActualChartBallIndex E)
    (hsmall : ∀ τ : b.support, ∀ u : StdSimplex ℝ (Fin 3),
      (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋2⦌) τ.1) u ∈
        actualChartBallCover (i τ))
    (τ : b.support)
    (y : (TopCat.toSSet.obj (TopCat.of E)) _⦋1⦌)
    (hy : y ∈ (singularBoundaryFinsupp (TopCat.of E) 1
      (Finsupp.single τ.1 1)).support) :
    ∀ γ ∈ (actualSharedEdgeRegular b i hsmall (Finsupp.single y 1)).support,
      ∀ t : ℝ, γ.toFun t ∈ actualChartBallCover (i τ) := by
  classical
  intro γ hγ t
  have hface := actualTriangleFace_mem_faceSet b τ y hy
  have hreg : actualSharedEdgeRegular b i hsmall (Finsupp.single y 1) =
      (actualChooseSharedEdge b i hsmall ⟨y, hface⟩).regular := by
    simp [actualSharedEdgeRegular, hface]
  rw [hreg] at hγ
  apply actualIncidentOpen_subset_ball b i τ y hy
  exact (actualChooseSharedEdge b i hsmall ⟨y, hface⟩).support γ hγ t

theorem actualSharedEdgeRegular_support_in_ball {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (b : ActualSingularTwoChains E)
    (i : b.support → ActualChartBallIndex E)
    (hsmall : ∀ τ : b.support, ∀ u : StdSimplex ℝ (Fin 3),
      (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋2⦌) τ.1) u ∈
        actualChartBallCover (i τ))
    (τ : b.support)
    (d : ActualSingularOneChains E)
    (hd : d.support ⊆ (singularBoundaryFinsupp (TopCat.of E) 1
      (Finsupp.single τ.1 1)).support) :
    ∀ γ ∈ (actualSharedEdgeRegular b i hsmall d).support,
      ∀ t : ℝ, γ.toFun t ∈ actualChartBallCover (i τ) := by
  classical
  intro γ hγ t
  have hrepr : d = ∑ y ∈ d.support, d y • Finsupp.single y 1 := by
    conv_lhs => rw [← Finsupp.sum_single d]
    simp [Finsupp.sum, Finsupp.smul_single]
  rw [hrepr] at hγ
  simp only [map_sum, map_smul] at hγ
  obtain ⟨y, hy, hγy⟩ := Finsupp.mem_support_finsetSum γ hγ
  have hγsingle := Finsupp.support_smul hγy
  exact actualSharedEdgeRegular_single_support_in_ball b i hsmall τ y (hd hy)
    γ hγsingle t

theorem actualSharedTriangleRegular_boundary_zero {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (b : ActualSingularTwoChains E)
    (i : b.support → ActualChartBallIndex E)
    (hsmall : ∀ τ : b.support, ∀ u : StdSimplex ℝ (Fin 3),
      (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋2⦌) τ.1) u ∈
        actualChartBallCover (i τ))
    (τ : b.support) :
    actualRegularChainBoundary
      (actualSharedEdgeRegular b i hsmall
        (singularBoundaryFinsupp (TopCat.of E) 1
          (Finsupp.single τ.1 1))) = 0 := by
  let d := singularBoundaryFinsupp (TopCat.of E) 1 (Finsupp.single τ.1 1)
  have hcorr := actualSharedEdgeCorrection_supported b i hsmall d
    (fun y hy => actualTriangleFace_mem_faceSet b τ y hy)
  have hsing : singularBoundaryFinsupp (TopCat.of E) 0
      (actualRegularChainsToSingular (actualSharedEdgeRegular b i hsmall d)) = 0 := by
    have h := congrArg (singularBoundaryFinsupp (TopCat.of E) 0) hcorr
    rw [singularBoundaryFinsupp_comp_zero, map_sub,
      singularBoundaryFinsupp_comp_zero] at h
    simpa using h
  have hchain := LinearMap.congr_fun
    (actualRegularChainsToSingular_boundary (E := E))
      (actualSharedEdgeRegular b i hsmall d)
  change singularBoundaryFinsupp (TopCat.of E) 0
    (actualRegularChainsToSingular (actualSharedEdgeRegular b i hsmall d)) =
    actualRegularPointsToSingular
      (actualRegularChainBoundary (actualSharedEdgeRegular b i hsmall d)) at hchain
  rw [hsing] at hchain
  exact actualRegularPointsToSingular_injective (by simpa using hchain.symm)

theorem actualSharedTriangleRegular_mem_relations {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (b : ActualSingularTwoChains E)
    (i : b.support → ActualChartBallIndex E)
    (hsmall : ∀ τ : b.support, ∀ u : StdSimplex ℝ (Fin 3),
      (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋2⦌) τ.1) u ∈
        actualChartBallCover (i τ))
    (τ : b.support) :
    (⟨actualSharedEdgeRegular b i hsmall
        (singularBoundaryFinsupp (TopCat.of E) 1 (Finsupp.single τ.1 1)),
      actualSharedTriangleRegular_boundary_zero b i hsmall τ⟩ :
        ActualRegularOneCycles E) ∈
      intervalLocalNormalizedRelations (E := E) := by
  let q := (i τ).q
  let c := (i τ).c
  let r := (i τ).r
  let x := (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋2⦌) τ.1)
    (StdSimplex.single 0)
  let z : Metric.ball c r := ⟨(chartAt ℂ q) x, (hsmall τ (StdSimplex.single 0)).2⟩
  apply actualChartBallRegularCycle_mem_relations q c r (i τ).target z
  · intro γ hγ t ht
    exact (actualSharedEdgeRegular_support_in_ball b i hsmall τ _
      Finset.Subset.rfl γ hγ t).1
  · intro γ hγ t ht
    exact (actualSharedEdgeRegular_support_in_ball b i hsmall τ _
      Finset.Subset.rfl γ hγ t).2

theorem actualSharedTwoChain_regularBoundary_mem_relations {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (b : ActualSingularTwoChains E)
    (i : b.support → ActualChartBallIndex E)
    (hsmall : ∀ τ : b.support, ∀ u : StdSimplex ℝ (Fin 3),
      (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋2⦌) τ.1) u ∈
        actualChartBallCover (i τ)) :
    ∃ a : ActualRegularOneCycles E,
      a.1 = actualSharedEdgeRegular b i hsmall
        (singularBoundaryFinsupp (TopCat.of E) 1 b) ∧
      a ∈ intervalLocalNormalizedRelations (E := E) := by
  classical
  let a : ActualRegularOneCycles E :=
    ∑ τ ∈ b.support.attach, (b τ.1) •
      (⟨actualSharedEdgeRegular b i hsmall
          (singularBoundaryFinsupp (TopCat.of E) 1
            (Finsupp.single τ.1 1)),
        actualSharedTriangleRegular_boundary_zero b i hsmall τ⟩ :
        ActualRegularOneCycles E)
  have ha : a ∈ intervalLocalNormalizedRelations (E := E) := by
    dsimp [a]
    apply Submodule.sum_mem
    intro τ hτ
    exact (intervalLocalNormalizedRelations (E := E)).smul_mem _
      (actualSharedTriangleRegular_mem_relations b i hsmall τ)
  refine ⟨a, ?_, ha⟩
  have hrepr : b = ∑ σ ∈ b.support, b σ • Finsupp.single σ 1 := by
    conv_lhs => rw [← Finsupp.sum_single b]
    simp [Finsupp.sum, Finsupp.smul_single]
  have hbd : singularBoundaryFinsupp (TopCat.of E) 1 b =
      ∑ τ ∈ b.support.attach, (b τ.1) •
        singularBoundaryFinsupp (TopCat.of E) 1
          (Finsupp.single τ.1 1) := by
    conv_lhs => rw [hrepr]
    simp only [map_sum, map_smul]
    rw [← Finset.sum_attach]
  have hmap := congrArg (actualSharedEdgeRegular b i hsmall) hbd
  rw [hmap]
  simp only [a, Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]

theorem actualSingularTwoBoundary_support_faceSet {E : Type}
    [TopologicalSpace E]
    (b : ActualSingularTwoChains E) :
    (singularBoundaryFinsupp (TopCat.of E) 1 b).support ⊆
      actualFaceSet b := by
  classical
  have hrepr : b = ∑ σ ∈ b.support, b σ • Finsupp.single σ 1 := by
    conv_lhs => rw [← Finsupp.sum_single b]
    simp [Finsupp.sum, Finsupp.smul_single]
  have hbd : singularBoundaryFinsupp (TopCat.of E) 1 b =
      ∑ σ ∈ b.support, b σ • singularBoundaryFinsupp (TopCat.of E) 1
        (Finsupp.single σ 1) := by
    conv_lhs => rw [hrepr]
    simp only [map_sum, map_smul]
  intro y hy
  rw [hbd] at hy
  obtain ⟨σ, hσ, hyσ⟩ := Finsupp.mem_support_finsetSum y hy
  exact Finset.mem_biUnion.mpr ⟨σ, hσ, Finsupp.support_smul hyσ⟩

theorem actualSharedTwoChain_correction {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (b : ActualSingularTwoChains E)
    (i : b.support → ActualChartBallIndex E)
    (hsmall : ∀ τ : b.support, ∀ u : StdSimplex ℝ (Fin 3),
      (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋2⦌) τ.1) u ∈
        actualChartBallCover (i τ)) :
    singularBoundaryFinsupp (TopCat.of E) 1
      (actualSharedEdgeCorrection b i hsmall
        (singularBoundaryFinsupp (TopCat.of E) 1 b)) =
      singularBoundaryFinsupp (TopCat.of E) 1 b -
        actualRegularChainsToSingular
          (actualSharedEdgeRegular b i hsmall
            (singularBoundaryFinsupp (TopCat.of E) 1 b)) :=
  actualSharedEdgeCorrection_supported b i hsmall _
    (fun y hy => actualSingularTwoBoundary_support_faceSet b hy)

end CanonicalDimensionTwo
