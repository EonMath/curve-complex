import Mathlib
open Set Topology
namespace CurveComplex.Hyperbolic
theorem actual_pants_cover_isometry_descends_locally_isometrically {P E : Type} [MetricSpace P] [MetricSpace E]
    (p : P → E) (hp : IsCoveringMap p) (hsurj : Function.Surjective p)
    (hmetric : ∀ x : P, ∃ U : Set P, IsOpen U ∧ x∈U ∧
      ∀ y∈U, ∀ z∈U, dist (p y) (p z) = dist y z)
    (j : P ≃ᵢ P) (J : E ≃ₜ E) (hdesc : ∀ x, J (p x) = p (j x)) :
    ∀ x : E, ∃ U : Set E, IsOpen U ∧ x∈U ∧
      ∀ y∈U, ∀ z∈U, dist (J y) (J z) = dist y z := by
  intro x
  obtain ⟨a,rfl⟩ := hsurj x
  obtain ⟨U,hU,haU,hmU⟩ := hmetric a
  obtain ⟨V,hV,hjaV,hmV⟩ := hmetric (j a)
  let W := U ∩ j ⁻¹' V
  have hW : IsOpen W := hU.inter (hV.preimage j.continuous)
  refine ⟨p '' W,hp.isOpenMap W hW,⟨a,⟨haU,hjaV⟩,rfl⟩,?_⟩
  rintro y ⟨b,hb,rfl⟩ z ⟨c,hc,rfl⟩
  rw [hdesc,hdesc,hmV (j b) hb.2 (j c) hc.2,j.dist_eq,
    ←hmU b hb.1 c hc.1]
end CurveComplex.Hyperbolic
