import CurveComplexGenusTwo.Dictionary.ArcVertexAPI
import CurveComplexGenusTwo.Dictionary.Circle33CanonicalEssential
namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] (M : HyperellipticModel E S)
/-- The chosen actual essential full preimage of a 3|3 circle. -/
noncomputable def circle33_essential_preimage (a : Circle33 M) : EssentialCurve E :=
  (M.circle33_preimage_essential_curve a).choose
/-- The actual full-preimage assignment on 3|3 circle isotopy classes. -/
noncomputable def circle33_vertex_map : Circle33Class M → Vertex E :=
  Quotient.lift
    (fun a => Quotient.mk (essentialCurveSetoid E) (M.circle33_essential_preimage a))
    (by
      intro a b hab
      apply Quotient.sound
      change AmbientIsotopy.Rel
        (M.circle33_preimage_essential_curve a).choose.val.image
        (M.circle33_preimage_essential_curve b).choose.val.image
      rw [(M.circle33_preimage_essential_curve a).choose_spec,
        (M.circle33_preimage_essential_curve b).choose_spec]
      exact M.marked_isotopy_preimage hab)
theorem circle33_essential_preimage_image (a : Circle33 M) :
    (M.circle33_essential_preimage a).val.image = M.cover.projection ⁻¹' a.val.image := by
  exact (M.circle33_preimage_essential_curve a).choose_spec
theorem circle33_vertex_map_mk (a : Circle33 M) :
    M.circle33_vertex_map (Quotient.mk (circle33Setoid M) a) =
      Quotient.mk (essentialCurveSetoid E) (M.circle33_essential_preimage a) := by
  rfl
theorem circle33_essential_preimage_complement_not_connected (a : Circle33 M) :
    ¬ IsConnected (M.circle33_essential_preimage a).val.imageᶜ := by
  rw [M.circle33_essential_preimage_image a]
  exact M.circle33_preimage_complement_not_connected a
/-- The actual source dictionary assignment, before proving bijectivity. -/
noncomputable def full_preimage_vertex_map :
    (NonLoopArcClass M ⊕ Circle33Class M) → Vertex E :=
  Sum.elim M.nonloop_arc_vertex_map M.circle33_vertex_map
theorem full_preimage_vertex_map_inl (a : NonLoopArc M) :
    M.full_preimage_vertex_map (Sum.inl (Quotient.mk (nonLoopArcSetoid M) a)) =
      Quotient.mk (essentialCurveSetoid E) (M.nonloop_arc_essential_preimage a) := by
  exact M.nonloop_arc_vertex_map_mk a
theorem full_preimage_vertex_map_inr (a : Circle33 M) :
    M.full_preimage_vertex_map (Sum.inr (Quotient.mk (circle33Setoid M) a)) =
      Quotient.mk (essentialCurveSetoid E) (M.circle33_essential_preimage a) := by
  rfl
end CurveComplex.HyperellipticModel

#print axioms CurveComplex.HyperellipticModel.circle33_essential_preimage

#print axioms CurveComplex.HyperellipticModel.circle33_vertex_map

#print axioms CurveComplex.HyperellipticModel.circle33_essential_preimage_image

#print axioms CurveComplex.HyperellipticModel.circle33_vertex_map_mk

#print axioms CurveComplex.HyperellipticModel.circle33_essential_preimage_complement_not_connected

#print axioms CurveComplex.HyperellipticModel.full_preimage_vertex_map

#print axioms CurveComplex.HyperellipticModel.full_preimage_vertex_map_inl

#print axioms CurveComplex.HyperellipticModel.full_preimage_vertex_map_inr
