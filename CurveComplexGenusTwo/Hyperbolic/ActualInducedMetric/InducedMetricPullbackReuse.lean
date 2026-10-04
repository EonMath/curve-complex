import CurveComplexGenusTwo.Hyperbolic.ActualCompactConeProducer

namespace CurveComplex.Hyperbolic
open Set Topology

-- Verbatim reuse of the APPROVED normalized source definition.
-- Integration must reuse the canonical declaration.
def TopologicalLocallyPullsBack
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [MetricSpace E] {P : Hexagon} (R : HexagonRegion P)
    (q : BranchedDoubleCover E S) (identify : S ≃ₜ DoubledPolygon R) : Prop :=
  ∀ x : E, x ∉ q.ramification →
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ∀ z ∈ U,
        dist y z = dist (identify (q.projection y))
          (identify (q.projection z))

end CurveComplex.Hyperbolic
