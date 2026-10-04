import CurveComplexGenusTwo.Topology.ActualJointGeodesicMinimum.GeodesicCleanReturn

namespace CurveComplex.Hyperbolic.JointMinimum

open Set Topology CurveComplex.LocalSurgery
open scoped Manifold UpperHalfPlane

section Surface

variable {E : Type} [TopologicalSpace E]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem geodesic_essential_curves_minimum_count_of_transverse
    (H : ClosedHyperbolicMetric E) (hE : IsGenus E 2)
    (a b : EssentialCurve E)
    (hageo : letI : MetricSpace E := H.metric; IsClosedGeodesic a.val.image)
    (hbgeo : letI : MetricSpace E := H.metric; IsClosedGeodesic b.val.image)
    (ht : Transverse a.val b.val) :
    (a.val.image ∩ b.val.image).ncard =
      geometricIntersection (Quotient.mk (essentialCurveSetoid E) a)
        (Quotient.mk (essentialCurveSetoid E) b) := by
  let : ClosedSurface E := hE.2.1.some
  apply fixed_comparison_minimum_of_no_clean_return a b ht
  intro u v huv f g hf hg hclean hhom
  exact closed_geodesics_no_homotopic_clean_return H a.val b.val hageo hbgeo
    u v huv f g hf hg hclean hhom

end Surface

end CurveComplex.Hyperbolic.JointMinimum
