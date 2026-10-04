import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ComplexMetricAtlasTransitionCandidate

namespace CurveComplex.Hyperbolic
open Set
open scoped ContDiff
variable {E : Type} [MetricSpace E]

theorem euclidean_metric_chart_transition_real_smooth
    (e d : OpenPartialHomeomorph E H2)
    (he : ∀ x ∈ e.source, ∀ y ∈ e.source, dist x y = dist (e x) (e y))
    (hd : ∀ x ∈ d.source, ∀ y ∈ d.source, dist x y = dist (d x) (d y)) :
    ContDiffOn ℝ ∞ ((inducedEuclideanHyperbolicChart e).symm.trans
      (inducedEuclideanHyperbolicChart d))
      ((inducedEuclideanHyperbolicChart e).symm.trans (inducedEuclideanHyperbolicChart d)).source := by
  let a := e.trans upperHalfPlaneComplexChart
  let b := d.trans upperHalfPlaneComplexChart
  let t := a.symm.trans b
  let u := (inducedEuclideanHyperbolicChart e).symm.trans (inducedEuclideanHyperbolicChart d)
  have hs : ContDiffOn ℝ ∞ t t.source := complex_metric_chart_transition_real_smooth e d he hd
  have hm : MapsTo complexEuclideanPlaneEquiv.symm u.source t.source := by
    intro x hx
    exact ⟨hx.1, hx.2⟩
  have hi := hs.comp complexEuclideanPlaneEquiv.symm.contDiff.contDiffOn hm
  simpa only [Function.comp_def] using!
    complexEuclideanPlaneEquiv.contDiff.comp_contDiffOn hi

end CurveComplex.Hyperbolic
