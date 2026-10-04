import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualPrimitiveDirectionFareyNormalization
namespace CurveComplexGenusTwo.Topology.PuncturedTorusCandidate
open CurveComplex

/-- Remaining geometric existence input. Essential means the actual embedded
circle does not bound an embedded closed disc, as in Foundations.Definitions. -/
theorem essential_torus_curve_has_primitive_slope (c : Curve Torus)
    (hc : Essential c) :
    ∃ s : FareySlope, AmbientIsotopy.Rel c.image
      (Set.range (torusWindingMap (slopeDirection s).1 (slopeDirection s).2)) := by
  obtain ⟨m,n,hprim,hmove⟩ := actual_original_essential_torus_has_primitive_ambient_straightening c hc
  obtain ⟨s,hs⟩ := actual_primitive_winding_has_farey_reference_image m n hprim
  exact ⟨s,hs ▸ hmove⟩

end CurveComplexGenusTwo.Topology.PuncturedTorusCandidate

#print axioms CurveComplexGenusTwo.Topology.PuncturedTorusCandidate.essential_torus_curve_has_primitive_slope
