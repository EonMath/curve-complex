import CurveComplexGenusTwo.Topology.ActualJointGeodesicMinimum.Providers
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.OriginalLoopDefinitions
import CurveComplexGenusTwo.Foundations.FoundationsIntersectionPort
import CurveComplexGenusTwo.Dictionary.Genus
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Homotopy.Lifting

import CurveComplexGenusTwo.Topology.ActualJointGeodesicMinimum.GeodesicMinimumCountReduction
import CurveComplexGenusTwo.Topology.ActualJointGeodesicMinimum.GeodesicTransverse

namespace CurveComplex.Hyperbolic.JointMinimum

open Set Topology CurveComplex.LocalSurgery
open scoped Manifold UpperHalfPlane

section Surface

variable {E : Type} [TopologicalSpace E]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem distinct_geodesic_essential_curves_realize_minimum_genus_two
    (H : ClosedHyperbolicMetric E) (hE : IsGenus E 2)
    (a b : EssentialCurve E)
    (hageo : letI : MetricSpace E := H.metric; IsClosedGeodesic a.val.image)
    (hbgeo : letI : MetricSpace E := H.metric; IsClosedGeodesic b.val.image)
    (hne : a.val.image ≠ b.val.image) :
    Transverse a.val b.val ∧
      (a.val.image ∩ b.val.image).ncard =
        geometricIntersection (Quotient.mk (essentialCurveSetoid E) a)
          (Quotient.mk (essentialCurveSetoid E) b) := by
  have ht := distinct_closed_geodesic_curves_transverse H a.val b.val hageo hbgeo hne
  exact ⟨ht, geodesic_essential_curves_minimum_count_of_transverse
    H hE a b hageo hbgeo ht⟩

end Surface

end CurveComplex.Hyperbolic.JointMinimum
