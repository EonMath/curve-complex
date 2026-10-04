import CurveComplexGenusTwo.Topology.ActualIntervalLocalComparison.IntervalLocalSharedFaces

open scoped Manifold ContDiff Bundle Simplicial
open Convexity CategoryTheory CurveComplexGenusTwo.CWHurewicz
open CanonicalDimensionTwo

namespace CanonicalDimensionTwo

theorem actualChartSmallTwoChain_sharedRegularize {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (b : ActualSingularTwoChains E)
    (hsmall : ∀ σ ∈ b.support, ∃ i : ActualChartBallIndex E,
      ∀ u : StdSimplex ℝ (Fin 3),
        (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋2⦌) σ) u ∈
          actualChartBallCover i) :
    ∃ a : ActualRegularOneCycles E,
      a ∈ intervalLocalNormalizedRelations (E := E) ∧
      ∃ c : ActualSingularTwoChains E,
        singularBoundaryFinsupp (TopCat.of E) 1 c =
          singularBoundaryFinsupp (TopCat.of E) 1 b -
            actualRegularChainsToSingular a.1 := by
  classical
  let i : b.support → ActualChartBallIndex E :=
    fun τ => Classical.choose (hsmall τ.1 τ.2)
  have hi : ∀ τ : b.support, ∀ u : StdSimplex ℝ (Fin 3),
      (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋2⦌) τ.1) u ∈
        actualChartBallCover (i τ) := by
    intro τ
    exact Classical.choose_spec (hsmall τ.1 τ.2)
  obtain ⟨a, haeq, ha⟩ :=
    actualSharedTwoChain_regularBoundary_mem_relations b i hi
  refine ⟨a, ha, actualSharedEdgeCorrection b i hi
    (singularBoundaryFinsupp (TopCat.of E) 1 b), ?_⟩
  rw [actualSharedTwoChain_correction b i hi, ← haeq]

theorem actualTwoChain_sharedRegularize_after_subdivision {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (b : ActualSingularTwoChains E) :
    ∃ k : ℕ, ∃ a : ActualRegularOneCycles E,
      a ∈ intervalLocalNormalizedRelations (E := E) ∧
      ∃ c : ActualSingularTwoChains E,
        singularBoundaryFinsupp (TopCat.of E) 1 c =
          singularBoundaryFinsupp (TopCat.of E) 1
            (singularBarycentricIterate (TopCat.of E) 2 k b) -
            actualRegularChainsToSingular a.1 := by
  obtain ⟨k, hk⟩ := actualSingularBarycentricIterate_chartSmall 2 b
  obtain ⟨a, ha, c, hc⟩ := actualChartSmallTwoChain_sharedRegularize
    (singularBarycentricIterate (TopCat.of E) 2 k b) hk
  exact ⟨k, a, ha, c, hc⟩

end CanonicalDimensionTwo
