import CurveComplexGenusTwo.Topology.ActualJointGeodesicMinimum.Providers
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.OriginalLoopDefinitions
import CurveComplexGenusTwo.Foundations.FoundationsIntersectionPort
import CurveComplexGenusTwo.Dictionary.Genus
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Homotopy.Lifting

import CurveComplexGenusTwo.Topology.ActualJointGeodesicMinimum.CleanReturnReductions
import CurveComplexGenusTwo.Topology.ActualJointGeodesicMinimum.FixedCoverTrace

namespace CurveComplex.Hyperbolic.JointMinimum

open Set Topology CurveComplex.LocalSurgery
open scoped Manifold UpperHalfPlane

section Surface

variable {E : Type} [TopologicalSpace E]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem closed_geodesics_no_homotopic_clean_return
    (H : ClosedHyperbolicMetric E) (a b : Curve E)
    (hageo : letI : MetricSpace E := H.metric; IsClosedGeodesic a.image)
    (hbgeo : letI : MetricSpace E := H.metric; IsClosedGeodesic b.image)
    (u v : E) (huv : u ≠ v) (f g : Path u v)
    (hf : Set.range f ⊆ a.image) (hg : Set.range g ⊆ b.image)
    (hclean : f '' Set.Ioo (0 : Interval) 1 ⊆ b.imageᶜ)
    (hhom : f.Homotopic g) : False := by
  obtain ⟨p, hquot, hp, hsurj, hlocal⟩ := common_component_developed_cover H u
  exact clean_return_impossible_on_developed_cover a b u v huv f g hf hg hclean hhom
    p hp hsurj
    (fun h himage => fixed_cover_geodesic_path_confined_to_line
      H a u hageo p hp hlocal h himage)
    (fun h himage => fixed_cover_geodesic_path_confined_to_line
      H b u hbgeo p hp hlocal h himage)

end Surface

end CurveComplex.Hyperbolic.JointMinimum
