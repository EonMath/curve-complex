import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualSurgeryPairTransport
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualFullStageEvent

namespace CurveComplex.HyperellipticModel.ArcSurgery
open CurveGenusTwo.Filtration CurveComplex.WeightedFlowScratch
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section
variable (M : HyperellipticModel E S) [LinearOrder (EssentialArcClass M)]
  (anchor : EssentialMarkedArc M) (G : AmbientIsotopy S)
  (hm : ∀ t p, p ∈ M.cover.branch → G.map (t,p) = p)
  (ha : ∀ t, (fun p => G.map (t,p)) '' anchor.val.image = anchor.val.image)

/-- The actual weighted event is unchanged by a genuinely transported minimum
position. Crossing order, raw trace and branch transport have been proved. -/
theorem actualSurgeryFaceEvent_position_transport
    (F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
    (x : FirstCrossing M anchor F P) (R : SurgeryPair M anchor F P x) (t : Interval)
    (σ : Finset (ActiveVertex (actualA M)))
    (hσ : σ ∈ (geometricComplex (actualA M)).faces)
    (hF : σ.image Subtype.val ⊆ F) (hx : x.selected.val ∈ σ.image Subtype.val)
    (z : CurveComplex.EdgeTime × CurveComplex.FiniteSimplex σ) :
    actualSurgeryFaceEvent M anchor F P x R σ hσ hF hx z =
      actualSurgeryFaceEvent M anchor F (timePosition M anchor F P G hm ha t)
        (transportFirstCrossing M anchor G hm ha F P x t)
        (transportSurgeryPair M anchor G hm ha F P x R t) σ hσ hF hx z := by
  let Q := timePosition M anchor F P G hm ha t
  let y := transportFirstCrossing M anchor G hm ha F P x t
  let R' := transportSurgeryPair M anchor G hm ha F P x R t
  let e : {b // b ∈ R.retained} ≃ {b // b ∈ R'.retained} := Equiv.refl _
  have hβ : R.retained.attach.image e = R'.retained.attach := by
    change R.retained.attach.image (fun b => b) = R.retained.attach
    exact Finset.image_id
  have hf (b : {b // b ∈ R.retained}) :
      activeArcClass M (vertex M (R'.pushed (e b))) =
        activeArcClass M (vertex M (R.pushed b)) := by
    apply Subtype.ext
    exact (marked_ambient_isotopy_prefix_preserves_class M G hm (R.pushed b)
      (timeTransport M G hm t (R.pushed b)) t (timeTransport_image M G hm t (R.pushed b))).symm
  unfold actualSurgeryFaceEvent
  exact branchingSurgeryPoint_equiv_branches (geometricComplex (actualA M)) σ hσ
    ⟨activeArcClass M x.selected.val, selectedActive_mem M anchor F P x σ hx⟩
    R.retained.attach R.nonempty.attach (fun b => activeArcClass M (vertex M (R.pushed b)))
    (actualSurgeryEvent_commonFace M anchor F P x R σ hσ hF hx)
    R'.retained.attach R'.nonempty.attach (fun b => activeArcClass M (vertex M (R'.pushed b)))
    (actualSurgeryEvent_commonFace M anchor F Q y R' σ hσ hF hx) e hβ hf z

 theorem actualSurgeryFullStageEvent_position_transport
    (F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
    (x : FirstCrossing M anchor F P) (R : SurgeryPair M anchor F P x) (t : Interval)
    (σ : Finset (ActiveVertex (actualA M)))
    (hσ : σ ∈ (geometricComplex (actualA M)).faces)
    (hF : σ.image Subtype.val ⊆ F) (hx : x.selected.val ∈ σ.image Subtype.val)
    (z : CurveComplex.EdgeTime × CurveComplex.RealizationPoint
      (CurveComplex.fullSubcomplex (geometricComplex (actualA M)) (· ∈ σ))) :
    actualSurgeryFullStageEvent M anchor F P x R σ hσ hF hx z =
      actualSurgeryFullStageEvent M anchor F (timePosition M anchor F P G hm ha t)
        (transportFirstCrossing M anchor G hm ha F P x t)
        (transportSurgeryPair M anchor G hm ha F P x R t) σ hσ hF hx z := by
  exact actualSurgeryFaceEvent_position_transport M anchor G hm ha F P x R t σ hσ hF hx
    (z.1,fullStageFaceCoordinates (geometricComplex (actualA M)) σ z.2)

/-- Independent new crossing and surgery-pair choices give the same event
throughout the actual anchor-relative isotopy. -/
theorem actualSurgeryFullStageEvent_transported_position_choice_independent
    (F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
    (x : FirstCrossing M anchor F P) (R : SurgeryPair M anchor F P x) (t : Interval)
    (y : FirstCrossing M anchor F (timePosition M anchor F P G hm ha t))
    (R' : SurgeryPair M anchor F (timePosition M anchor F P G hm ha t) y)
    (σ : Finset (ActiveVertex (actualA M)))
    (hσ : σ ∈ (geometricComplex (actualA M)).faces)
    (hF : σ.image Subtype.val ⊆ F)
    (hx : x.selected.val ∈ σ.image Subtype.val) (hy : y.selected.val ∈ σ.image Subtype.val)
    (z : CurveComplex.EdgeTime × CurveComplex.RealizationPoint
      (CurveComplex.fullSubcomplex (geometricComplex (actualA M)) (· ∈ σ))) :
    actualSurgeryFullStageEvent M anchor F P x R σ hσ hF hx z =
      actualSurgeryFullStageEvent M anchor F (timePosition M anchor F P G hm ha t) y R' σ hσ hF hy z := by
  exact (actualSurgeryFullStageEvent_position_transport M anchor G hm ha F P x R t σ hσ hF hx z).trans
    (actualSurgeryFullStageEvent_crossing_and_pair_choice_independent M anchor F
      (timePosition M anchor F P G hm ha t)
      (transportFirstCrossing M anchor G hm ha F P x t) y
      (transportSurgeryPair M anchor G hm ha F P x R t) R' σ hσ hF hx hy z)

end
end CurveComplex.HyperellipticModel.ArcSurgery
