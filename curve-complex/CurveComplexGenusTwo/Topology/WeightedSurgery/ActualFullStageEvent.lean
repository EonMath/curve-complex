import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualWeightedFaceCompatibilityHeaders
import CurveComplexGenusTwo.Topology.WeightedSurgery.FiniteRealizationTransport
import CurveComplexGenusTwo.Foundations.FullSubcomplex

open scoped BigOperators
namespace CurveComplex.WeightedFlowScratch
variable {V : Type*} [DecidableEq V]

noncomputable def fullStageFaceCoordinates (K : AbstractSimplicialComplex V)
    (σ : Finset V) (p : RealizationPoint (fullSubcomplex K (· ∈ σ))) : FiniteSimplex σ :=
  ⟨fun v => (fullToAmbient K (· ∈ σ) p).weight v,
    fun v => (fullToAmbient K (· ∈ σ) p).nonneg v,
    by
      simpa only [Finset.univ_eq_attach, Finset.sum_attach] using
        weight_sum_of_supported K (fullToAmbient K (· ∈ σ) p) σ
          (fun v hv => fullToAmbient_weight_of_not_property K (· ∈ σ) p v hv)⟩

theorem fullStageFaceCoordinates_continuous (K : AbstractSimplicialComplex V)
    (σ : Finset V) : Continuous (fullStageFaceCoordinates K σ) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro v
  exact (continuous_weight K v.val).comp (fullToAmbient_continuous K (· ∈ σ))

theorem faceInclusion_fullStageFaceCoordinates (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces)
    (p : RealizationPoint (fullSubcomplex K (· ∈ σ))) :
    faceInclusion K σ hσ (fullStageFaceCoordinates K σ p) =
      fullToAmbient K (· ∈ σ) p := by
  apply RealizationPoint.ext
  funext v
  by_cases hv : v ∈ σ
  · exact faceInclusion_weight_of_mem K σ hσ _ v hv
  · rw [faceInclusion_weight_of_not_mem K σ hσ _ v hv,
      fullToAmbient_weight_of_not_property K (· ∈ σ) p v hv]

end CurveComplex.WeightedFlowScratch
namespace CurveComplex.HyperellipticModel.ArcSurgery
open CurveGenusTwo.Filtration CurveComplex.WeightedFlowScratch
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable def actualSurgeryFullStageEvent (M : HyperellipticModel E S)
    [LinearOrder (EssentialArcClass M)] (anchor : EssentialMarkedArc M)
    (F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
    (x : FirstCrossing M anchor F P) (R : SurgeryPair M anchor F P x)
    (σ : Finset (ActiveVertex (actualA M)))
    (hσ : σ ∈ (geometricComplex (actualA M)).faces)
    (hF : σ.image Subtype.val ⊆ F) (hx : x.selected.val ∈ σ.image Subtype.val) :
    C(CurveComplex.EdgeTime × CurveComplex.RealizationPoint
      (CurveComplex.fullSubcomplex (geometricComplex (actualA M)) (· ∈ σ)),
      geometricRealization (actualA M)) :=
  (actualSurgeryFaceEvent M anchor F P x R σ hσ hF hx).comp
    ⟨fun z => (z.1, fullStageFaceCoordinates (geometricComplex (actualA M)) σ z.2),
      continuous_fst.prodMk
        ((fullStageFaceCoordinates_continuous (geometricComplex (actualA M)) σ).comp
          continuous_snd)⟩

theorem actualSurgeryFullStageEvent_starts (M : HyperellipticModel E S)
    [LinearOrder (EssentialArcClass M)] (anchor : EssentialMarkedArc M)
    (F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
    (x : FirstCrossing M anchor F P) (R : SurgeryPair M anchor F P x)
    (σ : Finset (ActiveVertex (actualA M)))
    (hσ : σ ∈ (geometricComplex (actualA M)).faces)
    (hF : σ.image Subtype.val ⊆ F) (hx : x.selected.val ∈ σ.image Subtype.val)
    (p : CurveComplex.RealizationPoint
      (CurveComplex.fullSubcomplex (geometricComplex (actualA M)) (· ∈ σ))) :
    actualSurgeryFullStageEvent M anchor F P x R σ hσ hF hx (0,p) =
      CurveComplex.fullToAmbient (geometricComplex (actualA M)) (· ∈ σ) p := by
  exact (actualSurgeryFaceEvent_starts M anchor F P x R σ hσ hF hx _).trans
    (faceInclusion_fullStageFaceCoordinates (geometricComplex (actualA M)) σ hσ p)

theorem actualSurgeryFullStageEvent_face_compatible (M : HyperellipticModel E S)
    [LinearOrder (EssentialArcClass M)] (anchor : EssentialMarkedArc M)
    (F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
    (x : FirstCrossing M anchor F P) (R : SurgeryPair M anchor F P x)
    (σ τ : Finset (ActiveVertex (actualA M)))
    (hσ : σ ∈ (geometricComplex (actualA M)).faces)
    (hτ : τ ∈ (geometricComplex (actualA M)).faces)
    (hFσ : σ.image Subtype.val ⊆ F) (hFτ : τ.image Subtype.val ⊆ F)
    (hxσ : x.selected.val ∈ σ.image Subtype.val)
    (hxτ : x.selected.val ∈ τ.image Subtype.val)
    (p : CurveComplex.RealizationPoint
      (CurveComplex.fullSubcomplex (geometricComplex (actualA M)) (· ∈ σ)))
    (q : CurveComplex.RealizationPoint
      (CurveComplex.fullSubcomplex (geometricComplex (actualA M)) (· ∈ τ)))
    (hpq : CurveComplex.fullToAmbient (geometricComplex (actualA M)) (· ∈ σ) p =
      CurveComplex.fullToAmbient (geometricComplex (actualA M)) (· ∈ τ) q)
    (t : CurveComplex.EdgeTime) :
    actualSurgeryFullStageEvent M anchor F P x R σ hσ hFσ hxσ (t,p) =
      actualSurgeryFullStageEvent M anchor F P x R τ hτ hFτ hxτ (t,q) := by
  apply actualSurgeryFaceEvent_face_compatible M anchor F P x R σ τ hσ hτ
    hFσ hFτ hxσ hxτ
  rw [faceInclusion_fullStageFaceCoordinates, faceInclusion_fullStageFaceCoordinates]
  exact hpq

theorem actualSurgeryFullStageEvent_zeroWeight_fixed (M : HyperellipticModel E S)
    [LinearOrder (EssentialArcClass M)] (anchor : EssentialMarkedArc M)
    (F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
    (x : FirstCrossing M anchor F P) (R : SurgeryPair M anchor F P x)
    (σ : Finset (ActiveVertex (actualA M)))
    (hσ : σ ∈ (geometricComplex (actualA M)).faces)
    (hF : σ.image Subtype.val ⊆ F) (hx : x.selected.val ∈ σ.image Subtype.val)
    (p : CurveComplex.RealizationPoint
      (CurveComplex.fullSubcomplex (geometricComplex (actualA M)) (· ∈ σ)))
    (t : CurveComplex.EdgeTime)
    (hp : (CurveComplex.fullToAmbient (geometricComplex (actualA M)) (· ∈ σ) p).weight
      (activeArcClass M x.selected.val) = 0) :
    actualSurgeryFullStageEvent M anchor F P x R σ hσ hF hx (t,p) =
      CurveComplex.fullToAmbient (geometricComplex (actualA M)) (· ∈ σ) p := by
  exact (actualSurgeryFaceEvent_zeroWeight_fixed M anchor F P x R σ hσ hF hx _ t hp).trans
    (faceInclusion_fullStageFaceCoordinates (geometricComplex (actualA M)) σ hσ p)

theorem actualSurgeryFullStageEvent_crossing_and_pair_choice_independent
    (M : HyperellipticModel E S) [LinearOrder (EssentialArcClass M)]
    (anchor : EssentialMarkedArc M) (F : Finset (EssentialArcClass M))
    (P : FinitePosition M anchor F) (x y : FirstCrossing M anchor F P)
    (R : SurgeryPair M anchor F P x) (R' : SurgeryPair M anchor F P y)
    (σ : Finset (ActiveVertex (actualA M)))
    (hσ : σ ∈ (geometricComplex (actualA M)).faces)
    (hF : σ.image Subtype.val ⊆ F)
    (hx : x.selected.val ∈ σ.image Subtype.val)
    (hy : y.selected.val ∈ σ.image Subtype.val)
    (z : CurveComplex.EdgeTime × CurveComplex.RealizationPoint
      (CurveComplex.fullSubcomplex (geometricComplex (actualA M)) (· ∈ σ))) :
    actualSurgeryFullStageEvent M anchor F P x R σ hσ hF hx z =
      actualSurgeryFullStageEvent M anchor F P y R' σ hσ hF hy z := by
  exact actualSurgeryFaceEvent_crossing_and_pair_choice_independent
    M anchor F P x y R R' σ hσ hF hx hy _

theorem actualSurgeryFullStageEvent_absent_selected_face
    (M : HyperellipticModel E S) [LinearOrder (EssentialArcClass M)]
    (anchor : EssentialMarkedArc M) (F : Finset (EssentialArcClass M))
    (P : FinitePosition M anchor F) (x : FirstCrossing M anchor F P)
    (R : SurgeryPair M anchor F P x)
    (σ τ : Finset (ActiveVertex (actualA M)))
    (hσ : σ ∈ (geometricComplex (actualA M)).faces)
    (hF : σ.image Subtype.val ⊆ F)
    (hx : x.selected.val ∈ σ.image Subtype.val)
    (habsent : activeArcClass M x.selected.val ∉ τ)
    (p : CurveComplex.RealizationPoint
      (CurveComplex.fullSubcomplex (geometricComplex (actualA M)) (· ∈ σ)))
    (q : CurveComplex.RealizationPoint
      (CurveComplex.fullSubcomplex (geometricComplex (actualA M)) (· ∈ τ)))
    (hpq : CurveComplex.fullToAmbient (geometricComplex (actualA M)) (· ∈ σ) p =
      CurveComplex.fullToAmbient (geometricComplex (actualA M)) (· ∈ τ) q)
    (t : CurveComplex.EdgeTime) :
    actualSurgeryFullStageEvent M anchor F P x R σ hσ hF hx (t,p) =
      CurveComplex.fullToAmbient (geometricComplex (actualA M)) (· ∈ τ) q := by
  have hz : (CurveComplex.fullToAmbient (geometricComplex (actualA M)) (· ∈ σ) p).weight
      (activeArcClass M x.selected.val) = 0 := by
    rw [hpq]
    exact CurveComplex.fullToAmbient_weight_of_not_property
      (geometricComplex (actualA M)) (· ∈ τ) q _ habsent
  exact (actualSurgeryFullStageEvent_zeroWeight_fixed M anchor F P x R σ hσ hF hx p t hz).trans hpq

theorem actualSurgery_retained_class_ne_selected (M : HyperellipticModel E S)
    [LinearOrder (EssentialArcClass M)] (anchor : EssentialMarkedArc M)
    (F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
    (x : FirstCrossing M anchor F P) (R : SurgeryPair M anchor F P x)
    (b : {b // b ∈ R.retained}) :
    activeArcClass M (vertex M (R.pushed b)) ≠ activeArcClass M x.selected.val := by
  intro h
  have hclass := congrArg Subtype.val h
  have hmin := P.minimal x.selected (R.pushed b) hclass (R.finite b)
  have hdec := R.decreases b
  omega

theorem actualSurgeryFullStageEvent_finishes_selected_zero
    (M : HyperellipticModel E S) [LinearOrder (EssentialArcClass M)]
    (anchor : EssentialMarkedArc M) (F : Finset (EssentialArcClass M))
    (P : FinitePosition M anchor F) (x : FirstCrossing M anchor F P)
    (R : SurgeryPair M anchor F P x)
    (σ : Finset (ActiveVertex (actualA M)))
    (hσ : σ ∈ (geometricComplex (actualA M)).faces)
    (hF : σ.image Subtype.val ⊆ F)
    (hx : x.selected.val ∈ σ.image Subtype.val)
    (p : CurveComplex.RealizationPoint
      (CurveComplex.fullSubcomplex (geometricComplex (actualA M)) (· ∈ σ))) :
    (actualSurgeryFullStageEvent M anchor F P x R σ hσ hF hx (1,p)).weight
      (activeArcClass M x.selected.val) = 0 := by
  let q := fullStageFaceCoordinates (geometricComplex (actualA M)) σ p
  have hf := actualSurgery_retained_class_ne_selected M anchor F P x R
  change (branchingSurgeryPoint (geometricComplex (actualA M)) σ hσ
    ⟨activeArcClass M x.selected.val, selectedActive_mem M anchor F P x σ hx⟩
    R.retained.attach R.nonempty.attach
    (fun b => activeArcClass M (vertex M (R.pushed b)))
    (actualSurgeryEvent_commonFace M anchor F P x R σ hσ hF hx) (1,q)).weight _ = 0
  simp only [branchingSurgeryPoint, surgeryUnnormalizedWeight, surgeryCutMass,
    hf, ite_false, Finset.sum_const_zero, add_zero]
  rw [CurveComplex.faceInclusion_weight_of_mem (geometricComplex (actualA M)) σ hσ q
    (activeArcClass M x.selected.val) (selectedActive_mem M anchor F P x σ hx)]
  simp

noncomputable def actualSurgeryFullStageHomotopy (M : HyperellipticModel E S)
    [LinearOrder (EssentialArcClass M)] (anchor : EssentialMarkedArc M)
    (F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
    (x : FirstCrossing M anchor F P) (R : SurgeryPair M anchor F P x)
    (σ : Finset (ActiveVertex (actualA M)))
    (hσ : σ ∈ (geometricComplex (actualA M)).faces)
    (hF : σ.image Subtype.val ⊆ F) (hx : x.selected.val ∈ σ.image Subtype.val) :
    ContinuousMap.Homotopy
      ⟨CurveComplex.fullToAmbient (geometricComplex (actualA M)) (· ∈ σ),
        CurveComplex.fullToAmbient_continuous (geometricComplex (actualA M)) (· ∈ σ)⟩
      ((actualSurgeryFullStageEvent M anchor F P x R σ hσ hF hx).comp
        ⟨fun p => (1,p), continuous_const.prodMk continuous_id⟩) where
  toFun := actualSurgeryFullStageEvent M anchor F P x R σ hσ hF hx
  continuous_toFun := (actualSurgeryFullStageEvent M anchor F P x R σ hσ hF hx).continuous
  map_zero_left := actualSurgeryFullStageEvent_starts M anchor F P x R σ hσ hF hx
  map_one_left := fun _ => rfl

end CurveComplex.HyperellipticModel.ArcSurgery
