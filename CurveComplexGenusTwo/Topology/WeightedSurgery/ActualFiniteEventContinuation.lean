import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualFullStageEvent

namespace CurveComplex.HyperellipticModel.ArcSurgery
open CurveGenusTwo.Filtration CurveComplex.WeightedFlowScratch
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Concrete geometry of one actual cut, with no homotopy or map field. -/
structure ActualEventCertificate (M : HyperellipticModel E S)
    [LinearOrder (EssentialArcClass M)] (anchor : EssentialMarkedArc M)
    (σ : Finset (ActiveVertex (actualA M))) where
  face : σ ∈ (geometricComplex (actualA M)).faces
  classes : Finset (EssentialArcClass M)
  position : FinitePosition M anchor classes
  crossing : FirstCrossing M anchor classes position
  surgery : SurgeryPair M anchor classes position crossing
  contains : σ.image Subtype.val ⊆ classes
  selected_mem : crossing.selected.val ∈ σ.image Subtype.val

variable (M : HyperellipticModel E S) [LinearOrder (EssentialArcClass M)]
  (anchor : EssentialMarkedArc M)
local notation "K" => geometricComplex (actualA M)
local notation "Stage" σ => CurveComplex.RealizationPoint (CurveComplex.fullSubcomplex K (· ∈ σ))

namespace ActualEventCertificate
variable {M anchor} {σ : Finset (ActiveVertex (actualA M))}

noncomputable def replacementVertices (c : ActualEventCertificate M anchor σ) :=
  c.surgery.retained.attach.image
    (fun b => activeArcClass M (vertex M (c.surgery.pushed b)))

noncomputable def nextFace (c : ActualEventCertificate M anchor σ) :=
  σ.erase (activeArcClass M c.crossing.selected.val) ∪ c.replacementVertices

theorem nextFace_mem (c : ActualEventCertificate M anchor σ) :
    c.nextFace ∈ (geometricComplex (actualA M)).faces := by
  have hc := actualSurgeryEvent_commonFace M anchor c.classes c.position c.crossing
    c.surgery σ c.face c.contains c.selected_mem
  apply ((geometricComplex (actualA M)).isRelLowerSet_faces hc).2
  · exact Finset.union_subset
      (Finset.Subset.trans (Finset.erase_subset _ _) Finset.subset_union_left) Finset.subset_union_right
  · exact Finset.union_nonempty.mpr (Or.inr
      (c.surgery.nonempty.attach.image _))

noncomputable def event (c : ActualEventCertificate M anchor σ) :=
  actualSurgeryFullStageEvent M anchor c.classes c.position c.crossing c.surgery
    σ c.face c.contains c.selected_mem

theorem endpoint_supported (c : ActualEventCertificate M anchor σ) (p : Stage σ) :
    c.event (1,p) ∈ CurveComplex.fullSupportLocus (geometricComplex (actualA M))
      (· ∈ c.nextFace) := by
  intro v hv
  by_cases he : v = activeArcClass M c.crossing.selected.val
  · subst v
    exact actualSurgeryFullStageEvent_finishes_selected_zero M anchor c.classes
      c.position c.crossing c.surgery σ c.face c.contains c.selected_mem p
  · have hout : v ∉ σ ∪ c.replacementVertices := by
      intro hm
      apply hv
      rcases Finset.mem_union.mp hm with hs | hr
      · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he, hs⟩)
      · exact Finset.mem_union_right _ hr
    change surgeryUnnormalizedWeight (geometricComplex (actualA M)) σ c.face
      ⟨activeArcClass M c.crossing.selected.val,
        selectedActive_mem M anchor c.classes c.position c.crossing σ c.selected_mem⟩
      c.surgery.retained.attach
      (fun b => activeArcClass M (vertex M (c.surgery.pushed b)))
      (1,fullStageFaceCoordinates (geometricComplex (actualA M)) σ p) v / _ = 0
    rw [surgeryUnnormalizedWeight_zero_outside _ _ _ _ _ _ _ v hout]
    exact zero_div _

noncomputable def endpointToNext (c : ActualEventCertificate M anchor σ) :
    C(Stage σ, Stage c.nextFace) :=
  ⟨fun p => CurveComplex.supportedToFull (geometricComplex (actualA M))
      (· ∈ c.nextFace) ⟨c.event (1,p), c.endpoint_supported p⟩,
    (CurveComplex.supportedToFull_continuous _ _).comp
      (((c.event.continuous.comp (continuous_const.prodMk continuous_id))).subtype_mk _)⟩

theorem endpointToNext_ambient (c : ActualEventCertificate M anchor σ) (p : Stage σ) :
    CurveComplex.fullToAmbient (geometricComplex (actualA M)) (· ∈ c.nextFace)
      (c.endpointToNext p) = c.event (1,p) :=
  CurveComplex.fullToAmbient_supportedToFull _ _ _

noncomputable def homotopyToNext (c : ActualEventCertificate M anchor σ) :
    ContinuousMap.Homotopy
      ⟨CurveComplex.fullToAmbient (geometricComplex (actualA M)) (· ∈ σ),
        CurveComplex.fullToAmbient_continuous _ _⟩
      ((⟨CurveComplex.fullToAmbient (geometricComplex (actualA M)) (· ∈ c.nextFace),
        CurveComplex.fullToAmbient_continuous _ _⟩ : C(Stage c.nextFace,
          geometricRealization (actualA M))).comp c.endpointToNext) :=
  (actualSurgeryFullStageHomotopy M anchor c.classes c.position c.crossing c.surgery
    σ c.face c.contains c.selected_mem).cast rfl (by
      apply ContinuousMap.ext
      intro p
      exact (c.endpointToNext_ambient p).symm)

theorem event_same_geometry_face_compatible
    {τ : Finset (ActiveVertex (actualA M))}
    (c : ActualEventCertificate M anchor σ) (d : ActualEventCertificate M anchor τ)
    (hc : c.classes = d.classes) (hP : HEq c.position d.position)
    (p : Stage σ) (q : Stage τ)
    (hpq : CurveComplex.fullToAmbient (geometricComplex (actualA M)) (· ∈ σ) p =
      CurveComplex.fullToAmbient (geometricComplex (actualA M)) (· ∈ τ) q)
    (t : CurveComplex.EdgeTime) : c.event (t,p) = d.event (t,q) := by
  unfold event
  cases c with
  | mk hσ Fc Pc xc Rc hFc hxc =>
    cases d with
    | mk hτ Fd Pd xd Rd hFd hxd =>
      dsimp only at hc hP
      cases hc
      cases hP
      have hcross := firstCrossing_unique M anchor Fc Pc xc xd
      cases hcross
      exact (actualSurgeryFullStageEvent_face_compatible M anchor Fc Pc xc Rc σ τ
        hσ hτ hFc hFd hxc hxd p q hpq t).trans
        (actualSurgeryFullStageEvent_crossing_and_pair_choice_independent M anchor Fc Pc
          xc xc Rc Rd τ hτ hFd hxd hxd (t,q))

end ActualEventCertificate

/-- A finite trace specifies actual cuts. Its next source is computed from the
previous cut, so no matching-output callback or homotopy is assumed. -/
inductive ActualFiniteEventTrace : (σ : Finset (ActiveVertex (actualA M))) → Type
  | stop (σ) : ActualFiniteEventTrace σ
  | cut {σ} (c : ActualEventCertificate M anchor σ)
      (tail : ActualFiniteEventTrace c.nextFace) : ActualFiniteEventTrace σ

namespace ActualFiniteEventTrace
variable {M anchor}

noncomputable def endpoint : {σ : Finset (ActiveVertex (actualA M))} →
    ActualFiniteEventTrace M anchor σ → C(Stage σ, geometricRealization (actualA M))
  | σ, .stop _ => ⟨CurveComplex.fullToAmbient (geometricComplex (actualA M)) (· ∈ σ),
      CurveComplex.fullToAmbient_continuous _ _⟩
  | _, .cut c tail => (endpoint tail).comp c.endpointToNext

noncomputable def homotopy : {σ : Finset (ActiveVertex (actualA M))} →
    (T : ActualFiniteEventTrace M anchor σ) → ContinuousMap.Homotopy
      ⟨CurveComplex.fullToAmbient (geometricComplex (actualA M)) (· ∈ σ),
        CurveComplex.fullToAmbient_continuous _ _⟩ T.endpoint
  | _, .stop _ => ContinuousMap.Homotopy.refl _
  | _, .cut c tail => c.homotopyToNext.trans
      (tail.homotopy.compContinuousMap c.endpointToNext)

/-- A zero-width first band passes the unchanged ambient point to its tail. -/
theorem cut_zeroWeight_input {σ : Finset (ActiveVertex (actualA M))}
    (c : ActualEventCertificate M anchor σ)
    (p : Stage σ)
    (hz : (CurveComplex.fullToAmbient (geometricComplex (actualA M)) (· ∈ σ) p).weight
      (activeArcClass M c.crossing.selected.val) = 0) :
    CurveComplex.fullToAmbient (geometricComplex (actualA M)) (· ∈ c.nextFace)
      (c.endpointToNext p) = CurveComplex.fullToAmbient
        (geometricComplex (actualA M)) (· ∈ σ) p := by
  rw [c.endpointToNext_ambient]
  exact actualSurgeryFullStageEvent_zeroWeight_fixed M anchor c.classes c.position
    c.crossing c.surgery σ c.face c.contains c.selected_mem p 1 hz

theorem homotopy_cut_zeroWeight_first_half
    {σ : Finset (ActiveVertex (actualA M))}
    (c : ActualEventCertificate M anchor σ)
    (tail : ActualFiniteEventTrace M anchor c.nextFace)
    (p : Stage σ)
    (hz : (CurveComplex.fullToAmbient (geometricComplex (actualA M)) (· ∈ σ) p).weight
      (activeArcClass M c.crossing.selected.val) = 0)
    (t : CurveComplex.EdgeTime) (ht : t.val ≤ 1/2) :
    (ActualFiniteEventTrace.cut c tail).homotopy (t,p) =
      CurveComplex.fullToAmbient (geometricComplex (actualA M)) (· ∈ σ) p := by
  simp only [homotopy, ContinuousMap.Homotopy.trans_apply, dite_eq_left ht]
  exact actualSurgeryFullStageEvent_zeroWeight_fixed M anchor c.classes c.position
    c.crossing c.surgery σ c.face c.contains c.selected_mem p _ hz

/-- Synchronization of actual cut geometry; this relation has no map,
homotopy, continuity, or face-independence assumption. -/
inductive SameGeometry : {σ τ : Finset (ActiveVertex (actualA M))} →
    ActualFiniteEventTrace M anchor σ → ActualFiniteEventTrace M anchor τ → Prop
  | stop (σ τ) : SameGeometry (.stop σ) (.stop τ)
  | cut {σ τ} (c : ActualEventCertificate M anchor σ)
      (d : ActualEventCertificate M anchor τ)
      (T : ActualFiniteEventTrace M anchor c.nextFace)
      (U : ActualFiniteEventTrace M anchor d.nextFace)
      (hc : c.classes = d.classes) (hP : HEq c.position d.position)
      (htail : SameGeometry T U) : SameGeometry (.cut c T) (.cut d U)

theorem endpoint_face_independent
    {σ τ : Finset (ActiveVertex (actualA M))}
    {T : ActualFiniteEventTrace M anchor σ} {U : ActualFiniteEventTrace M anchor τ}
    (h : SameGeometry T U) : ∀ (p : Stage σ) (q : Stage τ),
    CurveComplex.fullToAmbient (geometricComplex (actualA M)) (· ∈ σ) p =
      CurveComplex.fullToAmbient (geometricComplex (actualA M)) (· ∈ τ) q →
    T.endpoint p = U.endpoint q := by
  induction h with
  | stop σ τ => intro p q hpq; exact hpq
  | cut c d T U hc hP htail ih =>
    intro p q hpq
    apply ih
    rw [c.endpointToNext_ambient, d.endpointToNext_ambient]
    exact c.event_same_geometry_face_compatible d hc hP p q hpq 1

theorem homotopy_face_independent
    {σ τ : Finset (ActiveVertex (actualA M))}
    {T : ActualFiniteEventTrace M anchor σ} {U : ActualFiniteEventTrace M anchor τ}
    (h : SameGeometry T U) : ∀ (p : Stage σ) (q : Stage τ),
    CurveComplex.fullToAmbient (geometricComplex (actualA M)) (· ∈ σ) p =
      CurveComplex.fullToAmbient (geometricComplex (actualA M)) (· ∈ τ) q →
    ∀ t : CurveComplex.EdgeTime, T.homotopy (t,p) = U.homotopy (t,q) := by
  induction h with
  | stop σ τ => intro p q hpq t; exact hpq
  | cut c d T U hc hP htail ih =>
    intro p q hpq t
    simp only [homotopy, ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · exact c.event_same_geometry_face_compatible d hc hP p q hpq _
    · apply ih
      change CurveComplex.fullToAmbient (geometricComplex (actualA M)) (· ∈ c.nextFace)
        (c.endpointToNext p) = CurveComplex.fullToAmbient
          (geometricComplex (actualA M)) (· ∈ d.nextFace) (d.endpointToNext q)
      rw [c.endpointToNext_ambient, d.endpointToNext_ambient]
      exact c.event_same_geometry_face_compatible d hc hP p q hpq 1

end ActualFiniteEventTrace
end CurveComplex.HyperellipticModel.ArcSurgery
