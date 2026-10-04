import CurveComplexGenusTwo.Intersection.MarkedBarrier

namespace CurveComplex.HyperellipticModel

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- The actual stereographic image of the source arc has the embedded-interval
data required by the planar polygonal disk producer. -/
theorem NonLoopArc.chartedArcMap_continuous
    {M : HyperellipticModel E S} (a : NonLoopArc M)
    (p : S) (hp : p ∉ a.image) :
    Continuous (chartedArcMap a p hp) :=
  (M.puncturedPlane p).continuous.comp
    (Continuous.subtype_mk a.val.continuous _)

theorem NonLoopArc.chartedArcMap_injective
    {M : HyperellipticModel E S} (a : NonLoopArc M)
    (p : S) (hp : p ∉ a.image) :
    Function.Injective (chartedArcMap a p hp) := by
  intro t u htu
  apply a.injective
  exact congrArg Subtype.val ((M.puncturedPlane p).injective htu)

end CurveComplex.HyperellipticModel
