import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualUniformCellPhysicalGridSides
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Literal bounded coordinate carrier of the actual common strip. -/
noncomputable def actualStripProductCoordinates :
    (Interval × Icc (-1:ℝ) 1) ≃ₜ (Icc (0:ℝ) 1 ×ˢ Icc (-1:ℝ) 1) :=
  (Homeomorph.Set.prod (Icc (0:ℝ) 1) (Icc (-1:ℝ) 1)).symm
/-- An actual surface map whose values are in the strip has a constructed
continuous coordinate lift through the original embedding inverse. -/
theorem actual_common_strip_surface_coordinate_lift
    {X S : Type} [TopologicalSpace X] [TopologicalSpace S]
    (BC : Interval × Icc (-1:ℝ) 1 → S) (hBC : IsEmbedding BC)
    (F : C(X,S)) (hF : ∀ x,F x ∈ range BC) :
    ∃ q : C(X,Icc (0:ℝ) 1 ×ˢ Icc (-1:ℝ) 1),
      ∀ x,BC (actualStripProductCoordinates.symm (q x))=F x := by
  let Q : C(X,range BC) := ⟨fun x => ⟨F x,hF x⟩,F.continuous.subtype_mk hF⟩
  let q : C(X,Icc (0:ℝ) 1 ×ˢ Icc (-1:ℝ) 1) :=
    ⟨fun x => actualStripProductCoordinates (hBC.toHomeomorph.symm (Q x)),by fun_prop⟩
  refine ⟨q,?_⟩
  intro x
  change BC (actualStripProductCoordinates.symm
    (actualStripProductCoordinates (hBC.toHomeomorph.symm (Q x))))=F x
  rw [actualStripProductCoordinates.symm_apply_apply]
  exact congrArg Subtype.val (hBC.toHomeomorph.apply_symm_apply (Q x))
/-- Equality of actual surface values forces equality of the bounded strip
coordinates, including every fixed common endpoint. -/
theorem actual_common_strip_decode_injective
    {S : Type} [TopologicalSpace S]
    (BC : Interval × Icc (-1:ℝ) 1 → S) (hBC : IsEmbedding BC) :
    Function.Injective (fun q : (Icc (0:ℝ) 1 ×ˢ Icc (-1:ℝ) 1) =>
      BC (actualStripProductCoordinates.symm q)) := by
  exact hBC.injective.comp actualStripProductCoordinates.symm.injective
end CurveComplex.HyperellipticModel
