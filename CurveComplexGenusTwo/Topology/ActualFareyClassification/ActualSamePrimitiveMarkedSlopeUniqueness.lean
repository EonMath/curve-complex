import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualGivenBasisHorizontalSource
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualMarkedAmbientReverse
open Set Topology Schoenflies CurveComplex
/-- Two ORIGINAL essential torus curves with the same actual primitive winding
are ambient isotopic relative to an avoided puncture. Both finite positions,
both finite terminating reductions and the common reference are constructed. -/
theorem actual_same_primitive_winding_sources_are_marked_ambient_isotopic
    (a b : EssentialCurve (Circle×Circle)) (p : Plane)
    (ha : (Circle.exp (p 0),Circle.exp (p 1))∉a.val.image)
    (hb : (Circle.exp (p 0),Circle.exp (p 1))∉b.val.image)
    (m n : ℤ) (hgcd : m.gcd n=1) (F G : C(ℝ,ℝ×ℝ))
    (hF : ∀ x,(Circle.exp (F x).1,Circle.exp (F x).2)=a.val.map (Circle.exp x))
    (hG : ∀ x,(Circle.exp (G x).1,Circle.exp (G x).2)=b.val.map (Circle.exp x))
    (hFp : ∀ (k : ℤ) x,F (x+(k:ℝ)*(2*Real.pi))=
      ((F x).1+(k:ℝ)*(m:ℝ)*(2*Real.pi),(F x).2+(k:ℝ)*(n:ℝ)*(2*Real.pi)))
    (hGp : ∀ (k : ℤ) x,G (x+(k:ℝ)*(2*Real.pi))=
      ((G x).1+(k:ℝ)*(m:ℝ)*(2*Real.pi),(G x).2+(k:ℝ)*(n:ℝ)*(2*Real.pi))) :
    ∃ H : AmbientIsotopy (Circle×Circle),
      (∀ t,H.map (t,(Circle.exp (p 0),Circle.exp (p 1)))=(Circle.exp (p 0),Circle.exp (p 1))) ∧
      H.finalMap '' a.val.image=b.val.image := by
  let u := Int.gcdA m n
  let v := Int.gcdB m n
  have hbez : m*u+n*v=1 := by
    have hh := Int.gcd_eq_gcd_ab m n
    rw [hgcd] at hh
    exact hh.symm
  let e := actual_integer_basis_torus_homeomorph m n u v hbez
  obtain ⟨a',F',_,hAimage,hFproj,hFperiod⟩ :=
    actual_given_primitive_basis_has_horizontal_source_normalization a m n u v hbez F hF hFp
  obtain ⟨b',G',_,hBimage,hGproj,hGperiod⟩ :=
    actual_given_primitive_basis_has_horizontal_source_normalization b m n u v hbez G hG hGp
  let p' := integer_basis_plane_homeomorph m n u v hbez (p 0,p 1)
  have hp' : (Circle.exp (p' 0),Circle.exp (p' 1))=e (Circle.exp (p 0),Circle.exp (p 1)) :=
    (actual_integer_basis_torus_commutes_with_projection m n u v hbez (p 0,p 1)).symm
  have hAavoid : (Circle.exp (p' 0),Circle.exp (p' 1))∉a'.val.image := by
    rw [hAimage,hp']
    rintro ⟨z,hz,heq⟩
    exact ha (e.injective heq ▸ hz)
  have hBavoid : (Circle.exp (p' 0),Circle.exp (p' 1))∉b'.val.image := by
    rw [hBimage,hp']
    rintro ⟨z,hz,heq⟩
    exact hb (e.injective heq ▸ hz)
  obtain ⟨L,hLfix,hLimage⟩ := actual_original_horizontal_sources_are_marked_ambient_isotopic
    a' b' p' hAavoid hBavoid F' G' hFproj hGproj hFperiod hGperiod
  obtain ⟨H,hH⟩ := actual_homeomorph_conjugates_ambient_isotopy e L
  refine ⟨H,?_,?_⟩
  · intro t
    rw [hH,← hp',hLfix,hp']
    exact e.symm_apply_apply _
  · calc
      H.finalMap '' a.val.image=e.symm '' (L.finalMap '' (e '' a.val.image)) := by
        rw [image_image,image_image]
        apply image_congr
        intro z _
        exact hH ⟨1,by norm_num⟩ z
      _ = e.symm '' b'.val.image := by rw [← hAimage,hLimage]
      _ = b.val.image := by
        rw [hBimage,image_image]
        change (fun z : Circle×Circle => e.symm (e z)) '' b.val.image=b.val.image
        have hid : (fun z : Circle×Circle => e.symm (e z))=id := funext e.symm_apply_apply
        rw [hid,image_id]
#print axioms actual_same_primitive_winding_sources_are_marked_ambient_isotopic
