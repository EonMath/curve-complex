import Schoenflies.BoundaryContinuity2
import Schoenflies.SquareMover
namespace CurveComplex.LocalSurgery
open Set Schoenflies

theorem actualModelSquareClosedRegion :
    modelCurve∪inside modelCurve=Plane.closedSquare 0 1 := by
  rw [inside_modelCurve]
  ext z
  simp only [modelCurve,Plane.openSquare,Plane.closedSquare,Plane.supDist,sub_zero,mem_union,mem_setOf_eq]
  constructor
  · rintro (he | he)
    · exact he.le
    · exact he.le
  · intro he
    exact (eq_or_lt_of_le he)

theorem actualModelSquareClosedCapInterior {J : Set Plane}
    (hJ : IsJordanCurve J)
    (hbound : J∪inside J⊆modelCurve∪inside modelCurve) :
    inside J⊆inside modelCurve := by
  have hsub : inside J⊆Plane.closedSquare 0 1 := by
    intro z hz
    rw [←actualModelSquareClosedRegion]
    exact hbound (Or.inr hz)
  have hOpen : IsOpen (inside J) := (jordan_curve_theorem hJ).isOpen_inside
  have hInt := hOpen.subset_interior_iff.mpr hsub
  rw [Plane.interior_closedSquare] at hInt
  rw [inside_modelCurve]
  exact hInt
end CurveComplex.LocalSurgery
