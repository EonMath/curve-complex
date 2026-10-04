import CurveComplexGenusTwo.Topology.ActualIntervalLocalComparison.NormalizedRegularHOne

open scoped Manifold ContDiff Bundle Simplicial
open CanonicalDimensionTwo

namespace CanonicalDimensionTwo

structure IntervalLocalRegularChartTriangle (E : Type)
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] where
  edge01 : ActualRegularPath E
  edge12 : ActualRegularPath E
  edge20 : ActualRegularPath E
  chartCenter : E
  ballCenter : ℂ
  radius : ℝ
  edge_source : ∀ γ ∈ ({edge01, edge12, edge20} : Set (ActualRegularPath E)),
    ∀ t ∈ Set.Icc (0 : ℝ) 1, γ.toFun t ∈ (chartAt ℂ chartCenter).source
  edge_ball : ∀ γ ∈ ({edge01, edge12, edge20} : Set (ActualRegularPath E)),
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (chartAt ℂ chartCenter) (γ.toFun t) ∈ Metric.ball ballCenter radius
  ball_target : Metric.ball ballCenter radius ⊆ (chartAt ℂ chartCenter).target
  endpoint01 : edge01.toFun 1 = edge12.toFun 0
  endpoint12 : edge12.toFun 1 = edge20.toFun 0
  endpoint20 : edge20.toFun 1 = edge01.toFun 0

abbrev IntervalLocalRegularTwoChains (E : Type)
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :=
  IntervalLocalRegularChartTriangle E →₀ ℤ

noncomputable def intervalLocalRegularTwoBoundary {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    IntervalLocalRegularTwoChains E →ₗ[ℤ] ActualRegularOneChains E :=
  Finsupp.linearCombination ℤ (fun Δ : IntervalLocalRegularChartTriangle E =>
    Finsupp.single Δ.edge01 1 + Finsupp.single Δ.edge12 1 +
      Finsupp.single Δ.edge20 1)

theorem intervalLocalRegularTwoBoundary_boundary_zero {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    (actualRegularChainBoundary (E := E)).comp
      (intervalLocalRegularTwoBoundary (E := E)) = 0 := by
  apply Finsupp.lhom_ext
  intro Δ n
  simp only [LinearMap.comp_apply, LinearMap.zero_apply,
    intervalLocalRegularTwoBoundary, Finsupp.linearCombination_single,
    map_smul]
  rw [map_add, map_add, actualRegularChainBoundary_single,
    actualRegularChainBoundary_single, actualRegularChainBoundary_single,
    Δ.endpoint01, Δ.endpoint12, Δ.endpoint20]
  abel

noncomputable def intervalLocalRegularTwoBoundaryToCycles {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    IntervalLocalRegularTwoChains E →ₗ[ℤ] ActualRegularOneCycles E :=
  LinearMap.codRestrict (ActualRegularOneCycles E)
    (intervalLocalRegularTwoBoundary (E := E)) (fun c => by
      have h := LinearMap.congr_fun
        (intervalLocalRegularTwoBoundary_boundary_zero (E := E)) c
      simpa [ActualRegularOneCycles] using h)

def intervalLocalNormalizedRelationSet {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    Set (ActualRegularOneCycles E) :=
  Set.range (intervalLocalRegularTwoBoundaryToCycles (E := E)) ∪
  Set.range (actualRegularConstantCycle (E := E)) ∪
  Set.range (actualRegularReverseCycle (E := E)) ∪
  Set.range (actualRegularSubdivisionCycle (E := E))

noncomputable def intervalLocalNormalizedRelations {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    Submodule ℤ (ActualRegularOneCycles E) :=
  Submodule.span ℤ (intervalLocalNormalizedRelationSet (E := E))

abbrev IntervalLocalNormalizedRegularHOne (E : Type)
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :=
  ActualRegularOneCycles E ⧸ intervalLocalNormalizedRelations (E := E)

end CanonicalDimensionTwo
