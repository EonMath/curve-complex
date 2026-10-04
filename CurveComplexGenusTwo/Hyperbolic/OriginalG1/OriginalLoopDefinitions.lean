import CurveComplexGenusTwo.Topology.ActualGeometryRelease.ActualHyperbolicComponentCoverPlanePROVED
import CurveComplexGenusTwo.Foundations.CircleJordanAdapter
import CurveComplexGenusTwo.Topology.CapBandGeometry.GlobalCountableUniversalCoverHeader
import CurveComplexGenusTwo.Topology.CapBandGeometry.GlobalCoverDomainTransportHeader
import CurveComplexGenusTwo.Dictionary.MarkedSphere
import CurveComplexGenusTwo.Hyperbolic.ElementaryPolygon
import CurveComplexGenusTwo.Hyperbolic.HexagonAngles

namespace CurveComplex.Hyperbolic
open Filter Topology Set TopologicalSpace Bundle Path.Homotopic.Quotient CurveComplex.LocalSurgery
open scoped Manifold ContDiff UpperHalfPlane ENNReal unitInterval

variable {E : Type} [TopologicalSpace E]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

def FreeHomotopic (f g : C(Circle, E)) : Prop :=
  ∃ H : C(Circle × Interval, E),
    (∀ z : Circle, H (z, ⟨0, by norm_num⟩) = f z) ∧
    (∀ z : Circle, H (z, ⟨1, by norm_num⟩) = g z)

def EssentialLoop (f : C(Circle, E)) : Prop :=
  ¬ ∃ x : E, ∃ H : C(Circle × Interval, E),
    (∀ z : Circle, H (z, ⟨0, by norm_num⟩) = f z) ∧
    (∀ z : Circle, H (z, ⟨1, by norm_num⟩) = x)

def IsClosedGeodesic [MetricSpace E] (image : Set E) : Prop :=
  ∃ path : ℝ → E, ∃ period : ℝ,
    0 < period ∧ Continuous path ∧
      (∀ t, path (t + period) = path t) ∧
      Set.range path = image ∧
      ∀ t, ∃ ε : ℝ, 0 < ε ∧
        ∀ s u : ℝ, |s - t| < ε → |u - t| < ε →
          dist (path s) (path u) = |s - u|

end CurveComplex.Hyperbolic
