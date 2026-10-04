import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.ProperSignedStripClassExclusion
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualAnchorRelativeInverse

namespace CoherentEndpointMotion
open CurveComplex Set Topology Schoenflies

theorem boundary_preserving_homeomorph_inverse
    {X : Type*} [TopologicalSpace X] (B : Set X) (e : X ≃ₜ X)
    (hB : e '' B = B) : e.symm '' B = B := by
  calc
    e.symm '' B = e.symm '' (e '' B) := by rw [hB]
    _ = B := by
      rw [← Set.image_comp]
      simp only [Function.comp_def, e.symm_apply_apply]
      exact Set.image_id B

theorem boundary_preserving_homeomorph_mem
    {X : Type*} [TopologicalSpace X] (B : Set X) (e : X ≃ₜ X)
    (hB : e '' B = B) (x : X) : e x ∈ B ↔ x ∈ B := by
  constructor
  · intro hx
    have : e.symm (e x) ∈ e.symm '' B := ⟨e x,hx,rfl⟩
    simpa only [boundary_preserving_homeomorph_inverse B e hB,e.symm_apply_apply] using this
  · intro hx
    rw [← hB]
    exact ⟨x,hx,rfl⟩

theorem boundary_preserving_motion_compose
    {X : Type*} [TopologicalSpace X] (B : Set X) (H K : AmbientIsotopy X)
    (hH : ∀ t, (fun x => H.map (t,x)) '' B = B)
    (hK : ∀ t, (fun x => K.map (t,x)) '' B = B) :
    ∀ t, (fun x => (H.compose K).map (t,x)) '' B = B := by
  intro t
  change (fun x => K.map (t,H.map (t,x))) '' B = B
  rw [show (fun x => K.map (t,H.map (t,x))) =
    (fun x => K.map (t,x)) ∘ (fun x => H.map (t,x)) from rfl]
  rw [Set.image_comp,hH,hK]

/-- The original free-boundary ambient class relation is an equivalence.
This retains all-time setwise B preservation; no endpoint fixation is used. -/
theorem boundary_ambient_class_equivalence
    {X : Type} [TopologicalSpace X] (B : Set X) :
    Equivalence (fun A C : Set X => ∃ H : AmbientIsotopy X,
      (∀ t, (fun x => H.map (t,x)) '' B = B) ∧ H.finalMap '' A = C) := by
  refine ⟨?_,?_,?_⟩
  · intro A
    refine ⟨AmbientIsotopy.identity X,?_,?_⟩
    · intro t
      exact Set.image_id B
    · exact Set.image_id A
  · rintro A C ⟨H,hHB,hHC⟩
    refine ⟨actualIsotopyEndpointInverse H,actualIsotopyEndpointInverse_image H B hHB,?_⟩
    obtain ⟨e,he⟩ := H.homeomorphism_at 1
    have hefinal : (e : X → X) = H.finalMap := funext he
    have heA : e '' A = C := by rw [hefinal]; exact hHC
    have hfinal : (actualIsotopyEndpointInverse H).finalMap = e.symm := by
      funext x
      rw [actualIsotopyEndpointInverse_final]
      apply e.injective
      rw [e.apply_symm_apply]
      have h := CurveComplex.HyperellipticModel.ArcSurgery.timeHomeomorph_apply H 1
        ((CurveComplex.HyperellipticModel.ArcSurgery.timeHomeomorph H 1).symm x)
      rw [← he] at h
      exact h.symm.trans ((CurveComplex.HyperellipticModel.ArcSurgery.timeHomeomorph H 1).apply_symm_apply x)
    rw [hfinal,← heA,← Set.image_comp]
    simp only [Function.comp_def,e.symm_apply_apply]
    exact Set.image_id A
  · rintro A C D ⟨H,hHB,hHC⟩ ⟨K,hKB,hKD⟩
    refine ⟨H.compose K,boundary_preserving_motion_compose B H K hHB hKB,?_⟩
    rw [AmbientIsotopy.compose_finalMap,Set.image_comp,hHC,hKD]

/-- Literal disk essentiality and properness survive a common B-preserving
homeomorphism, so original family invariants can be carried through moves. -/
theorem boundary_homeomorph_transports_literal_essential_arc
    {X : Type} [TopologicalSpace X] (B : Set X) (e : X ≃ₜ X)
    (hB : e '' B = B) (a : C(Interval,X)) (ha : IsEmbedding a)
    (haends : a 0 ∈ B ∧ a 1 ∈ B)
    (haInterior : ∀ t ∈ Ioo (0 : Interval) 1, a t ∉ B)
    (hessential : ¬ ∃ c : C(Interval,X), IsEmbedding c ∧ (∀ t, c t ∈ B) ∧
      ∃ d : C(Metric.closedBall (0 : Plane) 1,X), IsEmbedding d ∧
        d '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} = range a ∪ range c) :
    let a' : C(Interval,X) := (⟨e,e.continuous⟩ : C(X,X)).comp a
    IsEmbedding a' ∧ (a' 0 ∈ B ∧ a' 1 ∈ B) ∧
      (∀ t ∈ Ioo (0 : Interval) 1, a' t ∉ B) ∧
      ¬ ∃ c : C(Interval,X), IsEmbedding c ∧ (∀ t, c t ∈ B) ∧
        ∃ d : C(Metric.closedBall (0 : Plane) 1,X), IsEmbedding d ∧
          d '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} = range a' ∪ range c := by
  intro a'
  refine ⟨e.isEmbedding.comp ha,?_,?_,?_⟩
  · exact ⟨(boundary_preserving_homeomorph_mem B e hB _).mpr haends.1,
      (boundary_preserving_homeomorph_mem B e hB _).mpr haends.2⟩
  · intro t ht hb
    exact haInterior t ht ((boundary_preserving_homeomorph_mem B e hB _).mp hb)
  · rintro ⟨c,hc,hcB,d,hd,hboundary⟩
    let c' : C(Interval,X) := (⟨e.symm,e.symm.continuous⟩ : C(X,X)).comp c
    let d' : C(Metric.closedBall (0 : Plane) 1,X) :=
      (⟨e.symm,e.symm.continuous⟩ : C(X,X)).comp d
    apply hessential
    refine ⟨c',e.symm.isEmbedding.comp hc,?_,d',e.symm.isEmbedding.comp hd,?_⟩
    · intro t
      apply (boundary_preserving_homeomorph_mem B e.symm
        (boundary_preserving_homeomorph_inverse B e hB) _).mpr
      exact hcB t
    · change (e.symm ∘ d) '' _ = range a ∪ range (e.symm ∘ c)
      rw [Set.image_comp,hboundary,Set.image_union,← Set.range_comp,← Set.range_comp]
      have he : e.symm ∘ a' = a := by funext t; exact e.symm_apply_apply (a t)
      rw [he]

/-- A common ambient move leaves every remaining individual class witness
available in the original free-boundary sense. -/
theorem boundary_motion_transports_individual_class
    {X : Type} [TopologicalSpace X] (B : Set X)
    (H : AmbientIsotopy X) (hHB : ∀ t, (fun x => H.map (t,x)) '' B = B)
    (A C : Set X)
    (hAC : ∃ K : AmbientIsotopy X,
      (∀ t, (fun x => K.map (t,x)) '' B = B) ∧ K.finalMap '' A = C) :
    ∃ K : AmbientIsotopy X,
      (∀ t, (fun x => K.map (t,x)) '' B = B) ∧ K.finalMap '' (H.finalMap '' A) = C := by
  exact (boundary_ambient_class_equivalence B).trans
    ((boundary_ambient_class_equivalence B).symm ⟨H,hHB,rfl⟩) hAC

/-- Class-distinctness survives applying one common ambient move to a family. -/
theorem boundary_motion_preserves_class_distinctness
    {X : Type} [TopologicalSpace X] (B : Set X)
    (H : AmbientIsotopy X) (hHB : ∀ t, (fun x => H.map (t,x)) '' B = B)
    (A C : Set X)
    (hAC : ¬ ∃ K : AmbientIsotopy X,
      (∀ t, (fun x => K.map (t,x)) '' B = B) ∧ K.finalMap '' A = C) :
    ¬ ∃ K : AmbientIsotopy X,
      (∀ t, (fun x => K.map (t,x)) '' B = B) ∧
      K.finalMap '' (H.finalMap '' A) = H.finalMap '' C := by
  intro h
  apply hAC
  exact (boundary_ambient_class_equivalence B).trans
    ((boundary_ambient_class_equivalence B).trans ⟨H,hHB,rfl⟩ h)
    ((boundary_ambient_class_equivalence B).symm ⟨H,hHB,rfl⟩)

end CoherentEndpointMotion
