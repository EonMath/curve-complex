import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualWeightedEvent
import CurveComplexGenusTwo.Topology.WeightedSurgery.WeightedEventFaceCompatibility
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualWeightedEventIndependence
import CurveComplexGenusTwo.Topology.WeightedSurgery.FirstCrossingUniqueness

namespace CurveComplex.HyperellipticModel.ArcSurgery

open CurveGenusTwo.Filtration CurveComplex.WeightedFlowScratch
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem actualSurgeryFaceEvent_crossing_and_pair_choice_independent (M : HyperellipticModel E S) [LinearOrder (EssentialArcClass M)]
    (anchor : EssentialMarkedArc M) (F : Finset (EssentialArcClass M))
    (P : FinitePosition M anchor F) (x y : FirstCrossing M anchor F P)
    (R : SurgeryPair M anchor F P x) (R' : SurgeryPair M anchor F P y)
    (σ : Finset (ActiveVertex (actualA M)))
    (hσ : σ ∈ (geometricComplex (actualA M)).faces)
    (hF : σ.image Subtype.val ⊆ F)
    (hx : x.selected.val ∈ σ.image Subtype.val)
    (hy : y.selected.val ∈ σ.image Subtype.val)
    (z : CurveComplex.EdgeTime × CurveComplex.FiniteSimplex σ) :
    actualSurgeryFaceEvent M anchor F P x R σ hσ hF hx z =
      actualSurgeryFaceEvent M anchor F P y R' σ hσ hF hy z := by
  have hxy := firstCrossing_unique M anchor F P x y
  subst y
  exact actualSurgeryFaceEvent_choice_independent M anchor F P x R R' σ hσ hF hx z

theorem actualSurgeryFaceEvent_face_compatible (M : HyperellipticModel E S) [LinearOrder (EssentialArcClass M)]
    (anchor : EssentialMarkedArc M) (F : Finset (EssentialArcClass M))
    (P : FinitePosition M anchor F) (x : FirstCrossing M anchor F P)
    (R : SurgeryPair M anchor F P x)
    (σ τ : Finset (ActiveVertex (actualA M)))
    (hσ : σ ∈ (geometricComplex (actualA M)).faces)
    (hτ : τ ∈ (geometricComplex (actualA M)).faces)
    (hFσ : σ.image Subtype.val ⊆ F) (hFτ : τ.image Subtype.val ⊆ F)
    (hxσ : x.selected.val ∈ σ.image Subtype.val)
    (hxτ : x.selected.val ∈ τ.image Subtype.val)
    (p : CurveComplex.FiniteSimplex σ) (q : CurveComplex.FiniteSimplex τ)
    (hpq : CurveComplex.faceInclusion (geometricComplex (actualA M)) σ hσ p =
      CurveComplex.faceInclusion (geometricComplex (actualA M)) τ hτ q)
    (t : CurveComplex.EdgeTime) :
    actualSurgeryFaceEvent M anchor F P x R σ hσ hFσ hxσ (t, p) =
      actualSurgeryFaceEvent M anchor F P x R τ hτ hFτ hxτ (t, q) := by
  unfold actualSurgeryFaceEvent
  exact branchingSurgeryPoint_face_compatibility (geometricComplex (actualA M))
    σ τ hσ hτ (activeArcClass M x.selected.val)
    (selectedActive_mem M anchor F P x σ hxσ)
    (selectedActive_mem M anchor F P x τ hxτ)
    R.retained.attach R.nonempty.attach
    (fun side => activeArcClass M (vertex M (R.pushed side)))
    (actualSurgeryEvent_commonFace M anchor F P x R σ hσ hFσ hxσ)
    (actualSurgeryEvent_commonFace M anchor F P x R τ hτ hFτ hxτ)
    p q hpq t

end CurveComplex.HyperellipticModel.ArcSurgery
