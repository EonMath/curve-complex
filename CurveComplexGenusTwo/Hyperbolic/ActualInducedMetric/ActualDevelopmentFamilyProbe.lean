import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualBranchMetricBaseDevelopmentCandidate

namespace CurveComplex.Hyperbolic
open Set
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]

/-- Internal chart family for the chain construction. Membership is proved
from actual chart producers; it is not an input to a source endpoint. -/
def actualCompactDevelopmentFamily (q : BranchedDoubleCover E S)
    (identify : S ≃ₜ Metric.GlueSpace (boundaryInclusion_isometry regularHexagonRegion)
      (boundaryInclusion_isometry regularHexagonRegion)) : Set (OpenPartialHomeomorph E H2) :=
  {e | ∃ c : H2, ∃ r : ℝ, 0 < r ∧ e.target = Metric.ball c r ∧
    ∀ y ∈ e.source, ∀ z ∈ e.source,
      dist (identify (q.projection y)) (identify (q.projection z)) ≤ dist (e y) (e z)}

end CurveComplex.Hyperbolic
