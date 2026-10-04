import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualEssentialMarkedFinitePosition

open Set Topology Schoenflies CurveComplex

/-- Literal homeomorphism transport of an original essential curve. -/
theorem actual_homeomorph_transports_essential_curve
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (a : EssentialCurve X) :
    ∃ b : EssentialCurve Y, (∀ z, b.val.map z=e (a.val.map z)) ∧
      b.val.image=e '' a.val.image := by
  let b : Curve Y := ⟨fun z => e (a.val.map z),e.isEmbedding.comp a.val.embedded⟩
  have hImage : b.image=e '' a.val.image := range_comp e a.val.map
  have hEss : Essential b := by
    rintro ⟨f,hf,hboundary⟩
    apply a.property
    refine ⟨(⟨e.symm,e.symm.continuous⟩ : C(Y,X)).comp f,e.symm.isEmbedding.comp hf,?_⟩
    change (e.symm ∘ f) '' _=a.val.image
    rw [image_comp,hboundary,hImage,image_image]
    have he : e.symm ∘ e=id := by funext x; exact e.symm_apply_apply x
    change (e.symm ∘ e) '' a.val.image=a.val.image
    rw [he,image_id]
  exact ⟨⟨b,hEss⟩,fun _ => rfl,hImage⟩

/-- Actual conjugation, retaining a literal all-time map formula. -/
theorem actual_homeomorph_conjugates_ambient_isotopy
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (H : AmbientIsotopy Y) :
    ∃ K : AmbientIsotopy X, ∀ t x, K.map (t,x)=e.symm (H.map (t,e x)) := by
  refine ⟨{ map := ⟨fun z => e.symm (H.map (z.1,e z.2)),
      e.symm.continuous.comp (H.map.continuous.comp
        (continuous_fst.prodMk (e.continuous.comp continuous_snd)))⟩,
            homeomorphism_at := ?_, at_zero := ?_ },fun _ _ => rfl⟩
  · intro t
    obtain ⟨h,hh⟩ := H.homeomorphism_at t
    exact ⟨(e.trans h).trans e.symm,fun x => congrArg e.symm (hh (e x))⟩
  · intro x
    change e.symm (H.map (⟨0,by norm_num⟩,e x))=x
    rw [H.at_zero,e.symm_apply_apply]

#print axioms actual_homeomorph_transports_essential_curve
#print axioms actual_homeomorph_conjugates_ambient_isotopy
