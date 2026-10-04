import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualHomotopyWindingLiftProducer
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualSamePrimitiveMarkedSlopeUniqueness
open Set Topology Schoenflies CurveComplex
open CurveComplexGenusTwo.Topology
/-- ORIGINAL same primitive homotopy class implies genuine puncture-relative
ambient uniqueness. Actual lifts, finite positions and reducing sequences are
constructed rather than added as source hypotheses. -/
theorem actual_same_primitive_homotopy_class_has_marked_ambient_uniqueness
    (a b : EssentialCurve (Circle×Circle)) (p : Plane)
    (ha : (Circle.exp (p 0),Circle.exp (p 1))∉a.val.image)
    (hb : (Circle.exp (p 0),Circle.exp (p 1))∉b.val.image)
    (m n : ℤ) (hgcd : m.gcd n=1)
    (hA : (⟨a.val.map,a.val.embedded.continuous⟩ : C(Circle,Circle×Circle)).Homotopic
      ⟨torusWindingMap m n,continuous_torusWindingMap m n⟩)
    (hB : (⟨b.val.map,b.val.embedded.continuous⟩ : C(Circle,Circle×Circle)).Homotopic
      ⟨torusWindingMap m n,continuous_torusWindingMap m n⟩) :
    ∃ H : AmbientIsotopy (Circle×Circle),
      (∀ t,H.map (t,(Circle.exp (p 0),Circle.exp (p 1)))=(Circle.exp (p 0),Circle.exp (p 1))) ∧
      H.finalMap '' a.val.image=b.val.image := by
  obtain ⟨F,hF,hFp⟩ := actual_homotopic_winding_source_has_exact_deck_lift a.val m n hA
  obtain ⟨G,hG,hGp⟩ := actual_homotopic_winding_source_has_exact_deck_lift b.val m n hB
  exact actual_same_primitive_winding_sources_are_marked_ambient_isotopic a b p ha hb m n hgcd
    F G hF hG hFp hGp
#print axioms actual_same_primitive_homotopy_class_has_marked_ambient_uniqueness
