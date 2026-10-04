import CurveComplexGenusTwo.Topology.ActualGenusTwoRecognition.ActualEntireAlternatingTotalNamedProofV14
import CurveComplexGenusTwo.Topology.ActualGenusTwoRecognition.OriginalClosedOrientableRecognitionNamedProofV1
import CurveComplexGenusTwo.Topology.ActualClosedOrientableHomology.OriginalClosedOrientableParameterExclusionProof
import ActualCover
import CurveComplexGenusTwo.Dictionary.MarkedSphere

namespace CurveComplex
open scoped Manifold ContDiff

/-- Exact source surface-recognition obligation left in original Main12.hmodel. -/
theorem genusTwo_homeomorphic_actual_alternating_total
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (hS : IsGenus S 2) :
    Nonempty (S ≃ₜ AlternatingSphereCover.Total) := by
  obtain ⟨p, hp, ⟨eS⟩⟩ := actual_original_genus_two_closed_orientable_recognition S hS
  have hp2 : p = 2 := actual_original_genus_two_closed_orientable_parameter_exclusion
    S hS p hp ⟨eS⟩
  subst p
  obtain ⟨eTotal⟩ := CurveComplexGenusTwo.SourceTopology.actual_entire_alternating_total_standard_genus_two_octagon
  exact ⟨eS.trans eTotal.symm⟩

end CurveComplex
