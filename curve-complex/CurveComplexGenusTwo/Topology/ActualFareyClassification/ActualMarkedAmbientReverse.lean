import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualOriginalHorizontalCanonicalMarkedReference
open Set Topology Schoenflies CurveComplex
/-- Reverse an actual ambient isotopy while retaining its actual fixed point. -/
theorem actual_point_fixed_ambient_isotopy_has_point_fixed_reverse
    {X : Type*} [TopologicalSpace X] (H : AmbientIsotopy X) (p : X)
    (hfix : ∀ t,H.map (t,p)=p) :
    ∃ R : AmbientIsotopy X,(∀ t,R.map (t,p)=p) ∧
      (∀ x,R.finalMap (H.finalMap x)=x) := by
  obtain ⟨e,he⟩ := H.homeomorphism_at ⟨1,by norm_num⟩
  have hep : e p=p := (he p).trans (hfix _)
  have hesp : e.symm p=p := by
    apply e.injective
    rw [e.apply_symm_apply,hep]
  let rev : Interval→Interval := fun t => ⟨1-t,by constructor <;> linarith [t.property.1,t.property.2]⟩
  have hrev : Continuous rev := (continuous_const.sub continuous_subtype_val).subtype_mk _
  have hrev0 : rev ⟨0,by norm_num⟩=⟨1,by norm_num⟩ := by apply Subtype.ext; norm_num [rev]
  have hrev1 : rev ⟨1,by norm_num⟩=⟨0,by norm_num⟩ := by apply Subtype.ext; norm_num [rev]
  let R : AmbientIsotopy X := {
    map := ⟨fun z => H.map (rev z.1,e.symm z.2),
      H.map.continuous.comp ((hrev.comp continuous_fst).prodMk
        (e.symm.continuous.comp continuous_snd))⟩
    homeomorphism_at := by
      intro t
      obtain ⟨f,hf⟩ := H.homeomorphism_at (rev t)
      exact ⟨e.symm.trans f,fun x => hf (e.symm x)⟩
    at_zero := by
      intro x
      change H.map (rev ⟨0,by norm_num⟩,e.symm x)=x
      rw [hrev0,← he,e.apply_symm_apply] }
  refine ⟨R,?_,?_⟩
  · intro t
    change H.map (rev t,e.symm p)=p
    rw [hesp,hfix]
  · intro x
    change H.map (rev ⟨1,by norm_num⟩,e.symm (H.finalMap x))=x
    rw [hrev1,H.at_zero]
    exact (congrArg e.symm (he x).symm).trans (e.symm_apply_apply x)

/-- Same actual normalized horizontal winding gives puncture-relative ambient
uniqueness for arbitrary original continuous essential embeddings. -/
theorem actual_original_horizontal_sources_are_marked_ambient_isotopic
    (a b : EssentialCurve (Circle×Circle)) (p : Plane)
    (ha : (Circle.exp (p 0),Circle.exp (p 1))∉a.val.image)
    (hb : (Circle.exp (p 0),Circle.exp (p 1))∉b.val.image)
    (F G : C(ℝ,ℝ×ℝ))
    (hF : ∀ x,(Circle.exp (F x).1,Circle.exp (F x).2)=a.val.map (Circle.exp x))
    (hG : ∀ x,(Circle.exp (G x).1,Circle.exp (G x).2)=b.val.map (Circle.exp x))
    (hFp : ∀ (k : ℤ) x,F (x+(k:ℝ)*(2*Real.pi))=((F x).1+(k:ℝ)*(2*Real.pi),(F x).2))
    (hGp : ∀ (k : ℤ) x,G (x+(k:ℝ)*(2*Real.pi))=((G x).1+(k:ℝ)*(2*Real.pi),(G x).2)) :
    ∃ H : AmbientIsotopy (Circle×Circle),
      (∀ t,H.map (t,(Circle.exp (p 0),Circle.exp (p 1)))=(Circle.exp (p 0),Circle.exp (p 1))) ∧
      H.finalMap '' a.val.image=b.val.image := by
  obtain ⟨L,hLfix,hLimage⟩ := actual_original_horizontal_source_has_canonical_marked_reference a p ha F hF hFp
  obtain ⟨R,hRfix,hRimage⟩ := actual_original_horizontal_source_has_canonical_marked_reference b p hb G hG hGp
  obtain ⟨S,hSfix,hSR⟩ := actual_point_fixed_ambient_isotopy_has_point_fixed_reverse R
    (Circle.exp (p 0),Circle.exp (p 1)) hRfix
  refine ⟨L.compose S,?_,?_⟩
  · intro t
    change S.map (t,L.map (t,(Circle.exp (p 0),Circle.exp (p 1))))=_
    rw [hLfix,hSfix]
  · change (S.finalMap ∘ L.finalMap) '' a.val.image=_
    rw [image_comp,hLimage,← hRimage,image_image]
    have hid : S.finalMap ∘ R.finalMap=id := funext hSR
    change (S.finalMap ∘ R.finalMap) '' b.val.image=b.val.image
    rw [hid,image_id]
#print axioms actual_point_fixed_ambient_isotopy_has_point_fixed_reverse
#print axioms actual_original_horizontal_sources_are_marked_ambient_isotopic
