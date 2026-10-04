import CurveComplexGenusTwo.Dictionary.Genus
import CurveComplexGenusTwo.Topology.ActualRegionalContactGeometry.RegionalFiniteContactGeometry

open CurveComplex Set Topology

namespace RegionalChordNormalization

/-- Pull a coordinate set back through the SAME partial chart into the actual F. -/
def chartPull {S : Type} [TopologicalSpace S] (F : Set S)
    (e : OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin 2)))
    (A : Set (EuclideanSpace ℝ (Fin 2))) : Set ↥F :=
  {y | y.val ∈ e.source ∧ e y.val ∈ A}

/-- The literal terminal parameterization used by the unchanged Stage A candidate. -/
def transport {X : Type*} [TopologicalSpace X]
    (K : AmbientIsotopy X) (a : C(Interval,X)) : C(Interval,X) :=
  ⟨fun t => K.map (1,a t),
    K.map.continuous.comp (continuous_const.prodMk a.continuous)⟩

end RegionalChordNormalization
