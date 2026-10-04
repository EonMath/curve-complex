import CurveComplexGenusTwo.Dictionary.CircleVertexAPI

namespace CurveComplex.HyperellipticModel

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- The literal full-preimage and complement specification of the ORIGINAL
Theorem 1.4, for the actual induced function; no bijectivity is built into it. -/
def DictionaryFullPreimageSpec (M : HyperellipticModel E S)
    (f : (NonLoopArcClass M ⊕ Circle33Class M) → Vertex E) : Prop :=
  (∀ a : NonLoopArc M, ∃ c : EssentialCurve E,
    c.val.image = M.cover.projection ⁻¹' a.image ∧
    f (Sum.inl (Quotient.mk (nonLoopArcSetoid M) a)) =
      Quotient.mk (essentialCurveSetoid E) c ∧ IsConnected c.val.imageᶜ) ∧
  (∀ a : Circle33 M, ∃ c : EssentialCurve E,
    c.val.image = M.cover.projection ⁻¹' a.val.image ∧
    f (Sum.inr (Quotient.mk (circle33Setoid M) a)) =
      Quotient.mk (essentialCurveSetoid E) c ∧ ¬ IsConnected c.val.imageᶜ)

theorem full_preimage_vertex_map_geometric_spec (M : HyperellipticModel E S) :
    DictionaryFullPreimageSpec M M.full_preimage_vertex_map := by
  constructor
  · intro a
    exact ⟨M.nonloop_arc_essential_preimage a,
      M.nonloop_arc_essential_preimage_image a,M.full_preimage_vertex_map_inl a,
      M.nonloop_arc_essential_preimage_complement_connected a⟩
  · intro a
    exact ⟨M.circle33_essential_preimage a,
      M.circle33_essential_preimage_image a,M.full_preimage_vertex_map_inr a,
      M.circle33_essential_preimage_complement_not_connected a⟩

theorem full_preimage_vertex_map_summands_disjoint (M : HyperellipticModel E S) :
    ∀ a : NonLoopArcClass M, ∀ b : Circle33Class M,
      M.nonloop_arc_vertex_map a ≠ M.circle33_vertex_map b := by
  intro a b
  induction a using Quotient.inductionOn with
  | _ a =>
    induction b using Quotient.inductionOn with
    | _ b =>
      intro he
      change Quotient.mk (essentialCurveSetoid E) (M.nonloop_arc_essential_preimage a) =
        Quotient.mk (essentialCurveSetoid E) (M.circle33_essential_preimage b) at he
      obtain ⟨I,hI⟩ := Quotient.exact he
      obtain ⟨h,hh⟩ := I.homeomorphism_at ⟨1,by norm_num⟩
      have hfinal : (h : E → E) = I.finalMap := funext hh
      have himage : h '' (M.nonloop_arc_essential_preimage a).val.image =
          (M.circle33_essential_preimage b).val.image := by
        rw [hfinal]
        exact hI
      have hc : IsConnected (M.circle33_essential_preimage b).val.imageᶜ := by
        rw [← himage,← h.image_compl]
        exact h.isConnected_image.mpr (M.nonloop_arc_essential_preimage_complement_connected a)
      exact M.circle33_essential_preimage_complement_not_connected b hc

/-- The exact geometric rule determines the actual function on EVERY quotient
class, independent of any bijectivity or invariant-representative assumption. -/
theorem full_preimage_rule_forces_vertex_map (M : HyperellipticModel E S)
    (f : (NonLoopArcClass M ⊕ Circle33Class M) → Vertex E)
    (hf : DictionaryFullPreimageSpec M f) : f = M.full_preimage_vertex_map := by
  funext x
  cases x with
  | inl a =>
    induction a using Quotient.inductionOn with
    | _ a =>
      obtain ⟨c,himage,hvalue,hconn⟩ := hf.1 a
      rw [hvalue,M.full_preimage_vertex_map_inl]
      apply Quotient.sound
      change AmbientIsotopy.Rel c.val.image (M.nonloop_arc_essential_preimage a).val.image
      rw [himage,M.nonloop_arc_essential_preimage_image]
      exact ambientIsotopy_equivalence.refl _
  | inr a =>
    induction a using Quotient.inductionOn with
    | _ a =>
      obtain ⟨c,himage,hvalue,hconn⟩ := hf.2 a
      rw [hvalue,M.full_preimage_vertex_map_inr]
      apply Quotient.sound
      change AmbientIsotopy.Rel c.val.image (M.circle33_essential_preimage a).val.image
      rw [himage,M.circle33_essential_preimage_image]
      exact ambientIsotopy_equivalence.refl _

theorem full_preimage_equivalence_unique (M : HyperellipticModel E S)
    (f g : (NonLoopArcClass M ⊕ Circle33Class M) ≃ Vertex E)
    (hf : DictionaryFullPreimageSpec M f) (hg : DictionaryFullPreimageSpec M g) : f = g := by
  apply Equiv.ext
  exact congrFun ((M.full_preimage_rule_forces_vertex_map f hf).trans
    (M.full_preimage_rule_forces_vertex_map g hg).symm)

end CurveComplex.HyperellipticModel
