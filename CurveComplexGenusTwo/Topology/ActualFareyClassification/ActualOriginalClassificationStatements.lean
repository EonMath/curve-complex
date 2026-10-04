import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualOriginalPunctureCorrectionStatements
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualOriginalFamilyUniquenessStatements
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualTranslatedPrimitivePuncturedUniqueness

namespace CurveComplexGenusTwo.Topology.PuncturedTorusCandidate
open CurveComplex

/-- Classification in the punctured surface for any representative family whose
filled isotopy classes are the standard primitive slopes. -/
theorem admissible_punctured_classification (p : Torus)
    (F : FareySlope → Curve (Punctured p))
    (hF : ∀ s, AmbientIsotopy.Rel (fill (F s)).image
      (Set.range (fun z : Circle =>
        (z ^ (slopeDirection s).1, z ^ (slopeDirection s).2)))) :
    ∀ c : Curve (Punctured p), Admissible c →
      ∃! s, AmbientIsotopy.Rel c.image (F s).image := by
  have hF' : ∀ s, AmbientIsotopy.Rel (fill (F s)).image
      (Set.range (torusWindingMap (slopeDirection s).1 (slopeDirection s).2)) := hF
  intro c hc
  obtain ⟨s,hcs⟩ := essential_torus_curve_has_primitive_slope (fill c) hc
  have hprim : (slopeDirection s).1.gcd (slopeDirection s).2=1 := by
    cases s with
    | none => decide
    | some q => exact rationalSlope_primitive q
  obtain ⟨a,d,hdparam,hcd⟩ := puncture_corrected_winding_isotopy p c
    (slopeDirection s).1 (slopeDirection s).2 hprim hcs
  obtain ⟨b,e,heparam,hFse⟩ := puncture_corrected_winding_isotopy p (F s)
    (slopeDirection s).1 (slopeDirection s).2 hprim (hF' s)
  have hde : AmbientIsotopy.Rel d.image e.image :=
    actual_translated_primitive_punctured_representatives_are_ambient_isotopic p d e a b
      (slopeDirection s).1 (slopeDirection s).2 hprim hdparam heparam
  have hcFs : AmbientIsotopy.Rel c.image (F s).image := ambientIsotopy_equivalence.trans hcd
    (ambientIsotopy_equivalence.trans hde (ambientIsotopy_equivalence.symm hFse))
  refine ⟨s,hcFs,?_⟩
  intro t hct
  exact punctured_slope_family_injective p F hF' t s
    (ambientIsotopy_equivalence.trans (ambientIsotopy_equivalence.symm hct) hcFs)

end CurveComplexGenusTwo.Topology.PuncturedTorusCandidate

#print axioms CurveComplexGenusTwo.Topology.PuncturedTorusCandidate.admissible_punctured_classification
