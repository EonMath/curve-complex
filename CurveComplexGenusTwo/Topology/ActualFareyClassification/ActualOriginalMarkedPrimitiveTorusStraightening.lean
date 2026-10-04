import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualPrimitiveWindingSourceNormalization
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualOriginalHorizontalBandGraphClosure
open Set Topology Schoenflies CurveComplex
open CurveComplexGenusTwo.Topology CurveComplexGenusTwo.Topology.PuncturedTorusCandidate
/-- The original essential source and an avoided puncture produce a genuine
puncture-relative primitive straightening. Its explicit translated reference is
a conclusion; the raw normalization is never asserted to fix the puncture. -/
theorem actual_original_marked_essential_torus_has_translated_primitive_straightening
    (c : Curve (Circle×Circle)) (hc : Essential c) (p : Plane)
    (hAvoid : (Circle.exp (p 0),Circle.exp (p 1))∉c.image) :
    ∃ m n : ℤ,m.gcd n=1 ∧∃ a : Circle×Circle,∃ H : AmbientIsotopy (Circle×Circle),
      (∀ t,H.map (t,(Circle.exp (p 0),Circle.exp (p 1)))=
        (Circle.exp (p 0),Circle.exp (p 1))) ∧
      H.finalMap '' c.image=range (fun z : Circle => a*torusWindingMap m n z) := by
  obtain ⟨m,n,F,_,hgcd,hproj,hperiod,_,_⟩ :=
    essential_torus_curve_has_primitive_deck_lift c hc
  let b : EssentialCurve (Circle×Circle) := ⟨c,hc⟩
  obtain ⟨u,v,hbez,b',G,_,himage,hGproj,hGperiod⟩ :=
    actual_primitive_winding_source_has_horizontal_normalization b m n hgcd F hproj hperiod
  let e := actual_integer_basis_torus_homeomorph m n u v hbez
  let p' := integer_basis_plane_homeomorph m n u v hbez (p 0,p 1)
  have hp' : (Circle.exp (p' 0),Circle.exp (p' 1))=e (Circle.exp (p 0),Circle.exp (p 1)) :=
    (actual_integer_basis_torus_commutes_with_projection m n u v hbez (p 0,p 1)).symm
  have hAvoid' : (Circle.exp (p' 0),Circle.exp (p' 1))∉b'.val.image := by
    rw [himage,hp']
    rintro ⟨z,hz,heq⟩
    exact hAvoid (e.injective heq ▸ hz)
  obtain ⟨L,h,hLfix,hLimage⟩ :=
    actual_original_horizontal_essential_has_marked_straight_reference b' p' hAvoid' G hGproj hGperiod
  obtain ⟨H,hH⟩ := actual_homeomorph_conjugates_ambient_isotopy e L
  let a : Circle×Circle := ((Circle.exp h)^(-v),(Circle.exp h)^u)
  have hreference : e.symm '' range (fun z : Circle => (z,Circle.exp h))=
      range (fun z : Circle => a*torusWindingMap m n z) := by
    rw [← range_comp]
    congr 1
    funext z
    apply Prod.ext <;>
      simp [e,a,actual_integer_basis_torus_homeomorph,torusWindingMap,mul_comm]
  refine ⟨m,n,hgcd,a,H,?_,?_⟩
  · intro t
    rw [hH,← hp',hLfix,hp']
    exact e.symm_apply_apply _
  · calc
      H.finalMap '' c.image=e.symm '' (L.finalMap '' (e '' b.val.image)) := by
        rw [image_image,image_image]
        apply image_congr
        intro z _
        exact hH ⟨1,by norm_num⟩ z
      _ = e.symm '' (L.finalMap '' b'.val.image) := by rw [← himage]
      _ = _ := by rw [hLimage,hreference]
#print axioms actual_original_marked_essential_torus_has_translated_primitive_straightening
