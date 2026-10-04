import CurveComplexGenusTwo.Filtration.Geometry.ActualArcFiltrationV3
import CurveComplexGenusTwo.Filtration.Geometry.ComponentGeometry
import CurveComplexGenusTwo.Topology.ArcStraightening
namespace CurveComplex.HyperellipticModel
open Set Schoenflies
theorem jordan_inside_complement_component {C : Set Plane} (hC : IsJordanCurve C) :
    IsComplementComponent C (inside C) := by
  have hs := jordan_curve_theorem hC
  refine ⟨hs.isConnected_inside.nonempty, hs.isConnected_inside, inside_subset_compl, ?_⟩
  intro V hV hsub hVc
  apply Subset.antisymm
  · apply hV.isPreconnected.subset_of_closure_inter_subset hs.isOpen_inside
    · obtain ⟨x, hx⟩ := hs.isConnected_inside.nonempty
      exact ⟨x, hsub hx, hx⟩
    · intro x hx
      rw [(IsRegionOf.inside C).closure_eq hs] at hx
      rcases hx.1 with hi | hc
      · exact hi
      · exact False.elim (hVc hx.2 hc)
  · exact hsub

end CurveComplex.HyperellipticModel
