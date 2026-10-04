import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualHorizontalRelativeReferenceBridge
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualOriginalHorizontalBandGraphClosure
open Set Topology Schoenflies CurveComplex
/-- An original normalized horizontal essential source moves relative to the
puncture onto the SAME source-independent reference at puncture height plus π. -/
theorem actual_original_horizontal_source_has_canonical_marked_reference
    (b : EssentialCurve (Circle×Circle)) (p : Plane)
    (hAvoid : (Circle.exp (p 0),Circle.exp (p 1))∉b.val.image)
    (F : C(ℝ,ℝ×ℝ))
    (hproj : ∀ x,(Circle.exp (F x).1,Circle.exp (F x).2)=b.val.map (Circle.exp x))
    (hp : ∀ (k : ℤ) x,F (x+(k:ℝ)*(2*Real.pi))=
      ((F x).1+(k:ℝ)*(2*Real.pi),(F x).2)) :
    ∃ H : AmbientIsotopy (Circle×Circle),
      (∀ t,H.map (t,(Circle.exp (p 0),Circle.exp (p 1)))=
        (Circle.exp (p 0),Circle.exp (p 1))) ∧
      H.finalMap '' b.val.image=range (fun z : Circle => (z,Circle.exp (p 1+Real.pi))) := by
  obtain ⟨L,h,hLfix,hLimage⟩ :=
    actual_original_horizontal_essential_has_marked_straight_reference b p hAvoid F hproj hp
  have htargetAvoid : (Circle.exp (p 0),Circle.exp (p 1))∉range (fun z : Circle => (z,Circle.exp h)) := by
    rw [← hLimage]
    rintro ⟨z,hz,heq⟩
    obtain ⟨e,he⟩ := L.homeomorphism_at ⟨1,by norm_num⟩
    have hzEq : z=(Circle.exp (p 0),Circle.exp (p 1)) :=
      e.injective (by rw [he,he]; exact heq.trans (hLfix ⟨1,by norm_num⟩).symm)
    exact hAvoid (hzEq ▸ hz)
  have hph : ∀ i : ℤ,p 1+(i:ℝ)*(2*Real.pi)≠h := by
    intro i hi
    apply htargetAvoid
    refine ⟨Circle.exp (p 0),?_⟩
    apply Prod.ext
    · rfl
    · rw [← hi,Circle.exp_add,Circle.exp_int_mul_two_pi,mul_one]
  have hpref : ∀ i : ℤ,p 1+(i:ℝ)*(2*Real.pi)≠p 1+Real.pi := by
    intro i hi
    have hh : (2:ℝ)*(i:ℝ)=1 := by nlinarith [Real.pi_pos]
    have hhZ : (2:ℤ)*i=1 := by exact_mod_cast hh
    omega
  obtain ⟨R,hRfix,hRimage⟩ :=
    actual_puncture_free_horizontal_references_are_relative_isotopic h (p 1+Real.pi) p hph hpref
  refine ⟨L.compose R,?_,?_⟩
  · intro t
    change R.map (t,L.map (t,(Circle.exp (p 0),Circle.exp (p 1))))=_
    rw [hLfix,hRfix]
  · change (R.finalMap ∘ L.finalMap) '' b.val.image=_
    rw [image_comp,hLimage,hRimage]
#print axioms actual_original_horizontal_source_has_canonical_marked_reference
