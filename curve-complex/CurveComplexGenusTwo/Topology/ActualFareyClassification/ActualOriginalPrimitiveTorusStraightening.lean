import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualPrimitiveWindingSourceNormalization
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualTorusCurveAvoidedPoint
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualHorizontalReferenceHeightRemoval
open Set Topology Schoenflies CurveComplex
open CurveComplexGenusTwo.Topology CurveComplexGenusTwo.Topology.PuncturedTorusCandidate
/-- Every ORIGINAL essential torus curve has an actual ambient straightening to
its source-produced primitive winding. Primitive lift, SL(2,Z) normalization,
finite positions and both finite reductions are all conclusions of producers. -/
theorem actual_original_essential_torus_has_primitive_ambient_straightening
    (c : Curve (Circle×Circle)) (hc : Essential c) :
    ∃ m n : ℤ, m.gcd n=1 ∧
      AmbientIsotopy.Rel c.image (range (torusWindingMap m n)) := by
  obtain ⟨m,n,F,_,hgcd,hproj,hperiod,_,_⟩ :=
    essential_torus_curve_has_primitive_deck_lift c hc
  let b : EssentialCurve (Circle×Circle) := ⟨c,hc⟩
  obtain ⟨u,v,hbez,b',G,hparam,himage,hGproj,hGperiod⟩ :=
    actual_primitive_winding_source_has_horizontal_normalization b m n hgcd F hproj hperiod
  obtain ⟨p,hpavoid⟩ := actual_essential_torus_curve_has_avoided_plane_point b'
  obtain ⟨L,h,_,hLimage⟩ :=
    actual_original_horizontal_essential_has_marked_straight_reference b' p hpavoid G hGproj hGperiod
  obtain ⟨R,hRimage⟩ := actual_horizontal_reference_has_zero_height_isotopy h
  let H := L.compose R
  have hHimage : H.finalMap '' b'.val.image=range (fun z : Circle => (z,1)) := by
    change (R.finalMap ∘ L.finalMap) '' b'.val.image=_
    rw [image_comp,hLimage,hRimage]
  let e := actual_integer_basis_torus_homeomorph m n u v hbez
  obtain ⟨K,hK⟩ := actual_homeomorph_conjugates_ambient_isotopy e H
  have hKfinal (z : Circle×Circle) : K.finalMap z=e.symm (H.finalMap (e z)) :=
    hK ⟨1,by norm_num⟩ z
  have hstandard : e.symm '' range (fun z : Circle => (z,1))=range (torusWindingMap m n) := by
    rw [← range_comp]
    congr 1
    funext z
    simp [e,actual_integer_basis_torus_homeomorph,torusWindingMap,Function.comp_def]
  refine ⟨m,n,hgcd,K,?_⟩
  calc
    K.finalMap '' c.image=e.symm '' (H.finalMap '' (e '' b.val.image)) := by
      rw [image_image,image_image]
      apply image_congr
      intro z _
      exact hKfinal z
    _ = e.symm '' (H.finalMap '' b'.val.image) := by rw [← himage]
    _ = range (torusWindingMap m n) := by rw [hHimage,hstandard]
#print axioms actual_original_essential_torus_has_primitive_ambient_straightening
