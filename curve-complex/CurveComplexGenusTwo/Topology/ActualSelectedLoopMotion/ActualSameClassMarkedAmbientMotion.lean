import CurveComplexGenusTwo.Dictionary.ArcEssentialDefinitions

namespace CurveComplex.HyperellipticModel

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem actual_same_class_marked_ambient_motion
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hclass : Quotient.mk (essentialArcSetoid M) a =
      Quotient.mk (essentialArcSetoid M) b) :
    ∃ K : AmbientIsotopy S,
      (∀ t z, z ∈ M.cover.branch → K.map (t,z) = z) ∧
      K.finalMap '' b.val.image = a.val.image := by
  have hab : MarkedIsotopyRel M a.val.image b.val.image :=
    Quotient.exact hclass
  exact (markedIsotopy_equivalence M).symm hab

end CurveComplex.HyperellipticModel
