import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualWeightedEvent
import CurveComplexGenusTwo.Topology.WeightedSurgery.WeightedBranchEquiv

namespace CurveComplex.HyperellipticModel.ArcSurgery

open CurveGenusTwo.Filtration CurveComplex.WeightedFlowScratch
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem actualSurgeryFaceEvent_choice_independent (M : HyperellipticModel E S)
    [LinearOrder (EssentialArcClass M)] (anchor : EssentialMarkedArc M)
    (F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
    (x : FirstCrossing M anchor F P) (R R' : SurgeryPair M anchor F P x)
    (σ : Finset (ActiveVertex (actualA M)))
    (hσ : σ ∈ (geometricComplex (actualA M)).faces)
    (hF : σ.image Subtype.val ⊆ F) (hx : x.selected.val ∈ σ.image Subtype.val)
    (z : CurveComplex.EdgeTime × CurveComplex.FiniteSimplex σ) :
    actualSurgeryFaceEvent M anchor F P x R σ hσ hF hx z =
      actualSurgeryFaceEvent M anchor F P x R' σ hσ hF hx z := by
  have hret := surgeryPair_retained_independent M anchor F P x R R'
  let e : {b // b ∈ R.retained} ≃ {b // b ∈ R'.retained} := {
    toFun := fun b => ⟨b.val, hret ▸ b.property⟩
    invFun := fun b => ⟨b.val, hret.symm ▸ b.property⟩
    left_inv := by intro b; rfl
    right_inv := by intro b; rfl }
  have hβ : R.retained.attach.image e = R'.retained.attach := by
    ext b
    constructor
    · intro _
      exact Finset.mem_attach _ _
    · intro _
      exact Finset.mem_image.mpr ⟨e.symm b, Finset.mem_attach _ _, e.apply_symm_apply b⟩
  have hf (b : {b // b ∈ R.retained}) :
      activeArcClass M (vertex M (R'.pushed (e b))) =
        activeArcClass M (vertex M (R.pushed b)) := by
    apply Subtype.ext
    exact (surgeryPair_pushOff_independent M anchor F P x R R' b.val b.property (e b).property).symm
  unfold actualSurgeryFaceEvent
  exact branchingSurgeryPoint_equiv_branches (geometricComplex (actualA M)) σ hσ
    ⟨activeArcClass M x.selected.val, selectedActive_mem M anchor F P x σ hx⟩
    R.retained.attach R.nonempty.attach (fun b => activeArcClass M (vertex M (R.pushed b)))
    (actualSurgeryEvent_commonFace M anchor F P x R σ hσ hF hx)
    R'.retained.attach R'.nonempty.attach (fun b => activeArcClass M (vertex M (R'.pushed b)))
    (actualSurgeryEvent_commonFace M anchor F P x R' σ hσ hF hx) e hβ hf z

end CurveComplex.HyperellipticModel.ArcSurgery
