import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualTranslatedPrimitiveSource
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualSamePrimitiveMarkedSlopeUniqueness
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualMarkedPunctureRestriction
open Set Topology Schoenflies CurveComplex
open CurveComplexGenusTwo.Topology CurveComplexGenusTwo.Topology.PuncturedTorusCandidate
/-- ANY two actual puncture-avoiding translated representatives with one
primitive literal winding parameter are ambient isotopic in the punctured
surface. Essentiality, exact lifts and the actual marked move are constructed. -/
theorem actual_translated_primitive_punctured_representatives_are_ambient_isotopic
    (p : Torus) (c d : Curve (Punctured p)) (a b : Torus) (m n : ℤ)
    (hgcd : m.gcd n=1)
    (hc : ∀ z,(c.map z : Torus)=a*torusWindingMap m n z)
    (hd : ∀ z,(d.map z : Torus)=b*torusWindingMap m n z) :
    AmbientIsotopy.Rel c.image d.image := by
  have hcEssential : Essential (fill c) := actual_translated_primitive_parameter_proves_essential
    (fill c) a m n hgcd hc
  have hdEssential : Essential (fill d) := actual_translated_primitive_parameter_proves_essential
    (fill d) b m n hgcd hd
  obtain ⟨F,hF,hFp⟩ := actual_translated_primitive_parameter_has_literal_deck_lift (fill c) a m n hc
  obtain ⟨G,hG,hGp⟩ := actual_translated_primitive_parameter_has_literal_deck_lift (fill d) b m n hd
  obtain ⟨α,hα⟩ := Circle.exp_surjective p.1
  obtain ⟨β,hβ⟩ := Circle.exp_surjective p.2
  let q := Plane.mk α β
  have hq : (Circle.exp (q 0),Circle.exp (q 1))=p := Prod.ext hα hβ
  have hcAvoid : (Circle.exp (q 0),Circle.exp (q 1))∉(fill c).image := by
    rw [hq]
    rintro ⟨z,hz⟩
    exact (c.map z).property hz
  have hdAvoid : (Circle.exp (q 0),Circle.exp (q 1))∉(fill d).image := by
    rw [hq]
    rintro ⟨z,hz⟩
    exact (d.map z).property hz
  obtain ⟨H,hHfix,hHimage⟩ := actual_same_primitive_winding_sources_are_marked_ambient_isotopic
    ⟨fill c,hcEssential⟩ ⟨fill d,hdEssential⟩ q hcAvoid hdAvoid m n hgcd F G hF hG hFp hGp
  have hfix : ∀ t,H.map (t,p)=p := by simpa only [hq] using hHfix
  obtain ⟨K,hK⟩ := actual_point_fixed_isotopy_restricts_to_puncture_complement H p hfix
  have hfill (e : Curve (Punctured p)) : Subtype.val '' e.image=(fill e).image := by
    change Subtype.val '' range e.map=range (fun z => (e.map z : Torus))
    exact (range_comp Subtype.val e.map).symm
  refine ⟨K,?_⟩
  apply image_injective.mpr Subtype.val_injective
  rw [image_image]
  calc
    (fun x => (K.finalMap x : Torus)) '' c.image=H.finalMap '' (Subtype.val '' c.image) := by
      rw [image_image]
      apply image_congr
      intro x _
      exact hK ⟨1,by norm_num⟩ x
    _ = (fill d).image := by rw [hfill,hHimage]
    _ = Subtype.val '' d.image := (hfill d).symm
#print axioms actual_translated_primitive_punctured_representatives_are_ambient_isotopic
