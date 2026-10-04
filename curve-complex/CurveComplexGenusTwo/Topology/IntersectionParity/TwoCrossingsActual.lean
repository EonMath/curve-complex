import CurveComplexGenusTwo.Topology.IntersectionParity.Parity
import CurveComplexGenusTwo.Topology.IntersectionParity.TwoCrossings

namespace CurveComplex.LocalSurgery

/-- Strict excess of the actual transverse count over geometric intersection
forces two distinct actual crossings, using proved geometric parity. -/
theorem two_crossings_of_geometric_intersection_excess
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (a b : EssentialCurve S) (ht : Transverse a.val b.val)
    (hexcess : geometricIntersection (Quotient.mk (essentialCurveSetoid S) a)
      (Quotient.mk (essentialCurveSetoid S) b) < ht.1.toFinset.card) :
    ∃ u v : S, u ∈ a.val.image ∩ b.val.image ∧
      v ∈ a.val.image ∩ b.val.image ∧ u ≠ v := by
  exact two_crossings_of_excess_and_parity a b ht hexcess
    (geometric_intersection_mod_two_actual a b ht)

end CurveComplex.LocalSurgery
