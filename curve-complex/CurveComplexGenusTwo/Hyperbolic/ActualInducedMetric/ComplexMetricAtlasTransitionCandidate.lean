import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.RealSmoothHyperbolicTransitionCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.HyperbolicMetricChartTransitionCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.InducedHyperbolicAtlasCandidate

namespace CurveComplex.Hyperbolic
open Set
open scoped ContDiff
variable {E : Type} [MetricSpace E]

theorem complex_metric_chart_transition_real_smooth
    (e d : OpenPartialHomeomorph E H2)
    (he : ∀ x ∈ e.source, ∀ y ∈ e.source, dist x y = dist (e x) (e y))
    (hd : ∀ x ∈ d.source, ∀ y ∈ d.source, dist x y = dist (d x) (d y)) :
    ContDiffOn ℝ ∞ ((e.trans upperHalfPlaneComplexChart).symm.trans
      (d.trans upperHalfPlaneComplexChart))
      ((e.trans upperHalfPlaneComplexChart).symm.trans (d.trans upperHalfPlaneComplexChart)).source := by
  let c := upperHalfPlaneComplexChart
  let p := e.symm.trans d
  let t := (e.trans c).symm.trans (d.trans c)
  have hmetric := hyperbolic_metric_chart_transition_distance e d he hd
  have hsmooth := real_smooth_hyperbolic_partial_isometry p hmetric
  have hsub : t.source ⊆ ((↑) : H2 → ℂ) '' p.source := by
    intro z hz
    have hzC : z ∈ c.target := hz.1.1
    have hzE : c.symm z ∈ e.target := hz.1.2
    have hzD : e.symm (c.symm z) ∈ d.source := hz.2.1
    refine ⟨c.symm z, ⟨hzE, hzD⟩, ?_⟩
    exact c.right_inv hzC
  apply (hsmooth.mono hsub).congr
  intro z hz
  have hzC : z ∈ c.target := hz.1.1
  have hcz : (c.symm z : ℂ) = z := c.right_inv hzC
  have hco : UpperHalfPlane.ofComplex z = c.symm z := by
    exact (congrArg UpperHalfPlane.ofComplex hcz.symm).trans
      (UpperHalfPlane.ofComplex_apply (c.symm z))
  change (d (e.symm (c.symm z)) : ℂ) = (p (UpperHalfPlane.ofComplex z) : ℂ)
  rw [hco]
  rfl

end CurveComplex.Hyperbolic
