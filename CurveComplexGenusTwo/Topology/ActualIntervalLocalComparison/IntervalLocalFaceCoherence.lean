import CurveComplexGenusTwo.Topology.ActualIntervalLocalComparison.IntervalLocalOpenEdgeRegularization

open scoped Manifold ContDiff Bundle Simplicial
open CategoryTheory CurveComplexGenusTwo.CWHurewicz
open CanonicalDimensionTwo

namespace CanonicalDimensionTwo

theorem actualRegularization_same_singular_chain_boundary {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (d : (TopCat.toSSet.obj (TopCat.of E)) _⦋1⦌ →₀ ℤ)
    (a a' : ActualRegularOneChains E)
    (b b' : (TopCat.toSSet.obj (TopCat.of E)) _⦋2⦌ →₀ ℤ)
    (hb : singularBoundaryFinsupp (TopCat.of E) 1 b =
      d - actualRegularChainsToSingular a)
    (hb' : singularBoundaryFinsupp (TopCat.of E) 1 b' =
      d - actualRegularChainsToSingular a') :
    actualRegularChainBoundary a = actualRegularChainBoundary a' := by
  have hsing : singularBoundaryFinsupp (TopCat.of E) 0
      (actualRegularChainsToSingular a - actualRegularChainsToSingular a') = 0 := by
    have hdiff : actualRegularChainsToSingular a - actualRegularChainsToSingular a' =
        singularBoundaryFinsupp (TopCat.of E) 1 (b' - b) := by
      rw [map_sub, hb', hb]
      abel
    rw [hdiff]
    exact singularBoundaryFinsupp_comp_zero (TopCat.of E) 0 (b' - b)
  rw [map_sub,
    show singularBoundaryFinsupp (TopCat.of E) 0
      (actualRegularChainsToSingular a) =
      actualRegularPointsToSingular (actualRegularChainBoundary a) from
        LinearMap.congr_fun (actualRegularChainsToSingular_boundary (E := E)) a,
    show singularBoundaryFinsupp (TopCat.of E) 0
      (actualRegularChainsToSingular a') =
      actualRegularPointsToSingular (actualRegularChainBoundary a') from
        LinearMap.congr_fun (actualRegularChainsToSingular_boundary (E := E)) a'] at hsing
  exact actualRegularPointsToSingular_injective (sub_eq_zero.mp hsing)

theorem actualChartBall_regularizations_equivalent {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (z : Metric.ball c r)
    (d : (TopCat.toSSet.obj (TopCat.of E)) _⦋1⦌ →₀ ℤ)
    (a a' : ActualRegularOneChains E)
    (b b' : (TopCat.toSSet.obj (TopCat.of E)) _⦋2⦌ →₀ ℤ)
    (hb : singularBoundaryFinsupp (TopCat.of E) 1 b =
      d - actualRegularChainsToSingular a)
    (hb' : singularBoundaryFinsupp (TopCat.of E) 1 b' =
      d - actualRegularChainsToSingular a')
    (has : ∀ γ ∈ a.support, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ.toFun t ∈ (chartAt ℂ q).source)
    (hab : ∀ γ ∈ a.support, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (chartAt ℂ q) (γ.toFun t) ∈ Metric.ball c r)
    (ha's : ∀ γ ∈ a'.support, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ.toFun t ∈ (chartAt ℂ q).source)
    (ha'b : ∀ γ ∈ a'.support, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (chartAt ℂ q) (γ.toFun t) ∈ Metric.ball c r) :
    (⟨a - a', by
      change actualRegularChainBoundary (a - a') = 0
      rw [map_sub, actualRegularization_same_singular_chain_boundary d a a' b b' hb hb']
      abel⟩ : ActualRegularOneCycles E) ∈
      intervalLocalNormalizedRelations (E := E) := by
  classical
  apply actualChartBallRegularCycle_mem_relations q c r htarget z
  · intro γ hγ t ht
    rcases Finset.mem_union.mp (Finsupp.support_sub hγ) with h | h
    · exact has γ h t ht
    · exact ha's γ h t ht
  · intro γ hγ t ht
    rcases Finset.mem_union.mp (Finsupp.support_sub hγ) with h | h
    · exact hab γ h t ht
    · exact ha'b γ h t ht

theorem actualSingularTriangle_boundary_image_subset {E : Type}
    [TopologicalSpace E]
    (σ : (TopCat.toSSet.obj (TopCat.of E)) _⦋2⦌)
    (U : Set E)
    (hσ : ∀ u : Convexity.StdSimplex ℝ (Fin 3),
      (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋2⦌) σ) u ∈ U)
    (y : (TopCat.toSSet.obj (TopCat.of E)) _⦋1⦌)
    (hy : y ∈ (singularBoundaryFinsupp (TopCat.of E) 1
      (Finsupp.single σ 1)).support) :
    ∀ u : Convexity.StdSimplex ℝ (Fin 2),
      (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌) y) u ∈ U := by
  rw [singularBoundaryFinsupp_single] at hy
  obtain ⟨i, _, hi⟩ := Finsupp.mem_support_finsetSum y hy
  have hface : y = (TopCat.toSSet.obj (TopCat.of E)).δ i σ := by
    have hsingle := Finsupp.support_smul hi
    simpa using Finsupp.support_single_subset hsingle
  subst y
  intro u
  rw [TopCat.toSSetObjEquiv_δ_apply]
  exact hσ _

theorem actualSingularTriangle_regularBoundary_mem_relations {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (σ : (TopCat.toSSet.obj (TopCat.of E)) _⦋2⦌)
    (hσ : ∀ u : Convexity.StdSimplex ℝ (Fin 3),
      (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋2⦌) σ) u ∈
        actualChartBallOpenSet q c r) :
    ∃ a : ActualRegularOneCycles E,
      a ∈ intervalLocalNormalizedRelations (E := E) ∧
      ∃ b : (TopCat.toSSet.obj (TopCat.of E)) _⦋2⦌ →₀ ℤ,
        singularBoundaryFinsupp (TopCat.of E) 1 b =
          singularBoundaryFinsupp (TopCat.of E) 1 (Finsupp.single σ 1) -
            actualRegularChainsToSingular a.1 := by
  let U := actualChartBallOpenSet q c r
  let d := singularBoundaryFinsupp (TopCat.of E) 1 (Finsupp.single σ 1)
  have hd : ∀ y ∈ d.support,
      ∃ i : ActualChartBallIndexInside E U,
        ∀ u : Convexity.StdSimplex ℝ (Fin 2),
          (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌) y) u ∈
            actualChartBallCover i.1 := by
    intro y hy
    refine ⟨⟨⟨q, c, r, htarget⟩, Set.Subset.rfl⟩, ?_⟩
    exact actualSingularTriangle_boundary_image_subset σ U hσ y hy
  obtain ⟨a, haU, b, hb⟩ := actualOpenChartSmallSingularChain_regularize U d hd
  have hsing : singularBoundaryFinsupp (TopCat.of E) 0
      (actualRegularChainsToSingular a) = 0 := by
    have h := congrArg (singularBoundaryFinsupp (TopCat.of E) 0) hb
    rw [singularBoundaryFinsupp_comp_zero, map_sub,
      singularBoundaryFinsupp_comp_zero] at h
    simpa using h
  have hchain : actualRegularChainBoundary a = 0 := by
    have h := LinearMap.congr_fun
      (actualRegularChainsToSingular_boundary (E := E)) a
    change singularBoundaryFinsupp (TopCat.of E) 0
      (actualRegularChainsToSingular a) =
      actualRegularPointsToSingular (actualRegularChainBoundary a) at h
    rw [hsing] at h
    exact actualRegularPointsToSingular_injective (by simpa using h.symm)
  let z : Metric.ball c r :=
    ⟨(chartAt ℂ q)
      ((TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋2⦌) σ)
        (Convexity.StdSimplex.single 0)),
      (hσ (Convexity.StdSimplex.single 0)).2⟩
  refine ⟨⟨a, hchain⟩, ?_, b, hb⟩
  apply actualChartBallRegularCycle_mem_relations q c r htarget z
  · intro γ hγ t ht
    exact (haU γ hγ t).1
  · intro γ hγ t ht
    exact (haU γ hγ t).2

end CanonicalDimensionTwo
