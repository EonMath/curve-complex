import ClosedHyperbolicCanonicalBridge
open Set Topology
open scoped Manifold ContDiff
namespace CurveComplex.Hyperbolic
theorem smooth_hyperbolic_chart_open_restriction {E : Type} [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [MetricSpace E]
    (c : SmoothHyperbolicChart E) (U : Set E) (hU : IsOpen U) :
    ∃ d : SmoothHyperbolicChart E,
      d.chart.source = c.chart.source ∩ U ∧ ∀ x, d.chart x = c.chart x := by
  let e := c.chart.toOpenPartialHomeomorph.restrOpen U hU
  let d : PartialDiffeomorph (𝓡 2) 𝓘(ℝ,ℂ) E ℂ ∞ := {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := c.chart.contMDiffOn_toFun.mono (by intro x hx; exact hx.1)
    contMDiffOn_invFun := c.chart.contMDiffOn_invFun.mono (by intro x hx; exact hx.1) }
  refine ⟨{ chart := d, upper := ?_, metric_preserving := ?_ },rfl,fun x => rfl⟩
  · intro x hx
    exact c.upper x hx.1
  · intro x y
    exact c.metric_preserving ⟨x.val,x.property.1⟩ ⟨y.val,y.property.1⟩
end CurveComplex.Hyperbolic
