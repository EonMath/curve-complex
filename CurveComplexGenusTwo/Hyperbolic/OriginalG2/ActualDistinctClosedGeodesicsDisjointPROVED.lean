import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ClosedHyperbolicCanonicalBridge
import CurveComplexGenusTwo.Hyperbolic.OriginalG2.SourceGeodesicLines

namespace CurveComplex.Hyperbolic
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Source Fact3.5(G2), restricted to the disjointness conclusion needed by
Haas's nondividing case. Distinct images are necessary: one geodesic class has
disjoint parallel representatives but its geodesic representatives coincide. -/
theorem actual_distinct_closed_geodesics_disjoint_of_disjoint_classes
    (H : ClosedHyperbolicMetric E) (a b a₀ b₀ : Curve E)
    (ha : Essential a) (hb : Essential b)
    (hageo : letI : MetricSpace E := H.metric; IsClosedGeodesic a.image)
    (hbgeo : letI : MetricSpace E := H.metric; IsClosedGeodesic b.image)
    (hne : a.image ≠ b.image)
    (haa : FreeHomotopic ⟨a.map,a.embedded.continuous⟩ ⟨a₀.map,a₀.embedded.continuous⟩)
    (hbb : FreeHomotopic ⟨b.map,b.embedded.continuous⟩ ⟨b₀.map,b₀.embedded.continuous⟩)
    (hdis : Disjoint a₀.image b₀.image) : Disjoint a.image b.image := by
  exact source_actual_distinct_closed_geodesics_disjoint_of_disjoint_classes
    H a b a₀ b₀ ha hb hageo hbgeo hne haa hbb hdis

#print axioms actual_distinct_closed_geodesics_disjoint_of_disjoint_classes

end CurveComplex.Hyperbolic
