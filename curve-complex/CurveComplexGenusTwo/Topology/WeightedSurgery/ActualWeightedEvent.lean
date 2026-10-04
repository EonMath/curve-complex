import CurveComplexGenusTwo.Topology.WeightedSurgery.SurgeryCommonSimplex
import CurveComplexGenusTwo.Topology.WeightedSurgery.WeightedSurgeryEvent
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualFiniteNullhomotopy
import CurveComplexGenusTwo.Topology.WeightedSurgery.SurgeryChoiceIndependence

namespace CurveComplex.HyperellipticModel.ArcSurgery

open CurveGenusTwo.Filtration CurveComplex.WeightedFlowScratch
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem selectedActive_mem (M : HyperellipticModel E S)
    [LinearOrder (EssentialArcClass M)] (anchor : EssentialMarkedArc M)
    (F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
    (x : FirstCrossing M anchor F P) (σ : Finset (ActiveVertex (actualA M)))
    (hx : x.selected.val ∈ σ.image Subtype.val) :
    activeArcClass M x.selected.val ∈ σ := by
  obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hx
  have h : v = activeArcClass M x.selected.val := Subtype.ext heq
  exact h ▸ hv

theorem actualSurgeryEvent_commonFace (M : HyperellipticModel E S)
    [LinearOrder (EssentialArcClass M)] (anchor : EssentialMarkedArc M)
    (F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
    (x : FirstCrossing M anchor F P) (R : SurgeryPair M anchor F P x)
    (σ : Finset (ActiveVertex (actualA M)))
    (hσ : σ ∈ (geometricComplex (actualA M)).faces)
    (hF : σ.image Subtype.val ⊆ F) (hx : x.selected.val ∈ σ.image Subtype.val) :
    σ ∪ R.retained.attach.image (fun side => activeArcClass M (vertex M (R.pushed side))) ∈
      (geometricComplex (actualA M)).faces := by
  have hclass := hσ.2
  change IsArcSimplex M (σ.image Subtype.val) at hclass
  have h := surgery_common_simplex M anchor F P x R (σ.image Subtype.val) hF hclass hx
  unfold replacementClasses at h
  have hdec : instDecidableEqEssentialArcClass_arcSurgeryProducers M =
      (inferInstance : DecidableEq (EssentialArcClass M)) := Subsingleton.elim _ _
  rw [hdec] at h
  refine ⟨Finset.union_nonempty.mpr (Or.inl hσ.1), ?_⟩
  change IsArcSimplex M ((σ ∪ R.retained.attach.image
    (fun side => activeArcClass M (vertex M (R.pushed side)))).image Subtype.val)
  simpa only [Finset.image_union, Finset.image_image, Function.comp_def, activeArcClass] using h

/-- A genuine weighted local surgery event, with both retained branches and
normalization after discarded inessential branches. Duplicate quotient labels
receive the sum of their branch masses. -/
noncomputable def actualSurgeryFaceEvent (M : HyperellipticModel E S)
    [LinearOrder (EssentialArcClass M)] (anchor : EssentialMarkedArc M)
    (F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
    (x : FirstCrossing M anchor F P) (R : SurgeryPair M anchor F P x)
    (σ : Finset (ActiveVertex (actualA M)))
    (hσ : σ ∈ (geometricComplex (actualA M)).faces)
    (hF : σ.image Subtype.val ⊆ F) (hx : x.selected.val ∈ σ.image Subtype.val) :
    C(CurveComplex.EdgeTime × CurveComplex.FiniteSimplex σ,
      geometricRealization (actualA M)) := by
  let selected : σ := ⟨activeArcClass M x.selected.val, selectedActive_mem M anchor F P x σ hx⟩
  let f := fun side : {side // side ∈ R.retained} => activeArcClass M (vertex M (R.pushed side))
  have hne : R.retained.attach.Nonempty := by
    obtain ⟨b, hb⟩ := R.nonempty
    exact ⟨⟨b, hb⟩, Finset.mem_attach _ _⟩
  have hτ := actualSurgeryEvent_commonFace M anchor F P x R σ hσ hF hx
  exact ⟨branchingSurgeryPoint (geometricComplex (actualA M)) σ hσ selected
    R.retained.attach hne f hτ,
    branchingSurgeryPoint_continuous (geometricComplex (actualA M)) σ hσ selected
      R.retained.attach hne f hτ⟩

theorem actualSurgeryFaceEvent_starts (M : HyperellipticModel E S)
    [LinearOrder (EssentialArcClass M)] (anchor : EssentialMarkedArc M)
    (F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
    (x : FirstCrossing M anchor F P) (R : SurgeryPair M anchor F P x)
    (σ : Finset (ActiveVertex (actualA M)))
    (hσ : σ ∈ (geometricComplex (actualA M)).faces)
    (hF : σ.image Subtype.val ⊆ F) (hx : x.selected.val ∈ σ.image Subtype.val)
    (p : CurveComplex.FiniteSimplex σ) :
    actualSurgeryFaceEvent M anchor F P x R σ hσ hF hx (0, p) =
      CurveComplex.faceInclusion (geometricComplex (actualA M)) σ hσ p := by
  unfold actualSurgeryFaceEvent
  exact branchingSurgeryPoint_zero (geometricComplex (actualA M)) σ hσ
    ⟨activeArcClass M x.selected.val, selectedActive_mem M anchor F P x σ hx⟩
    R.retained.attach R.nonempty.attach (fun side => activeArcClass M (vertex M (R.pushed side)))
    (actualSurgeryEvent_commonFace M anchor F P x R σ hσ hF hx) p

theorem actualSurgeryFaceEvent_zeroWeight_fixed (M : HyperellipticModel E S)
    [LinearOrder (EssentialArcClass M)] (anchor : EssentialMarkedArc M)
    (F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
    (x : FirstCrossing M anchor F P) (R : SurgeryPair M anchor F P x)
    (σ : Finset (ActiveVertex (actualA M)))
    (hσ : σ ∈ (geometricComplex (actualA M)).faces)
    (hF : σ.image Subtype.val ⊆ F) (hx : x.selected.val ∈ σ.image Subtype.val)
    (p : CurveComplex.FiniteSimplex σ) (t : CurveComplex.EdgeTime)
    (hp : p.val ⟨activeArcClass M x.selected.val, selectedActive_mem M anchor F P x σ hx⟩ = 0) :
    actualSurgeryFaceEvent M anchor F P x R σ hσ hF hx (t, p) =
      CurveComplex.faceInclusion (geometricComplex (actualA M)) σ hσ p := by
  unfold actualSurgeryFaceEvent
  exact branchingSurgeryPoint_zeroWeight_fixed (geometricComplex (actualA M)) σ hσ
    ⟨activeArcClass M x.selected.val, selectedActive_mem M anchor F P x σ hx⟩
    R.retained.attach R.nonempty.attach (fun side => activeArcClass M (vertex M (R.pushed side)))
    (actualSurgeryEvent_commonFace M anchor F P x R σ hσ hF hx) t p hp

end CurveComplex.HyperellipticModel.ArcSurgery
