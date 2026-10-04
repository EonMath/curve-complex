import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualClampedBandEvent
import CurveComplexGenusTwo.CWHurewicz.GeometricContinuation.WeightedIntersectionClockHeaders

namespace CurveComplex.HyperellipticModel.ArcSurgery
open CurveGenusTwo.Filtration CurveComplex.WeightedFlowScratch
open scoped BigOperators
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
variable {M : HyperellipticModel E S} [LinearOrder (EssentialArcClass M)]
  {anchor : EssentialMarkedArc M}
local notation "K" => geometricComplex (actualA M)
local notation "Stage" σ => CurveComplex.RealizationPoint (CurveComplex.fullSubcomplex K (· ∈ σ))
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace ActualEventCertificate
variable {σ : Finset (ActiveVertex (actualA M))}

noncomputable def selectedMass (c : ActualEventCertificate M anchor σ) (p : Stage σ) : ℝ :=
  (CurveComplex.fullToAmbient K (· ∈ σ) p).weight (activeArcClass M c.crossing.selected.val)

theorem selectedMass_nonneg (c : ActualEventCertificate M anchor σ) (p : Stage σ) :
    0 ≤ c.selectedMass p := (CurveComplex.fullToAmbient K (· ∈ σ) p).nonneg _

theorem selectedMass_continuous (c : ActualEventCertificate M anchor σ) :
    Continuous c.selectedMass :=
  (CurveComplex.continuous_weight K _).comp (CurveComplex.fullToAmbient_continuous K _)

noncomputable def endpointScale (c : ActualEventCertificate M anchor σ) (p : Stage σ) : ℝ :=
  1 + ((c.surgery.retained.attach.card : ℝ)-1) * c.selectedMass p

theorem endpointScale_positive (c : ActualEventCertificate M anchor σ) (p : Stage σ) :
    0 < c.endpointScale p := by
  have hn : (1 : ℝ) ≤ c.surgery.retained.attach.card := by
    exact_mod_cast Finset.card_pos.mpr c.surgery.nonempty.attach
  have hp := mul_nonneg (sub_nonneg.mpr hn) (c.selectedMass_nonneg p)
  unfold endpointScale
  linarith

theorem endpointScale_continuous (c : ActualEventCertificate M anchor σ) :
    Continuous c.endpointScale :=
  continuous_const.add (continuous_const.mul c.selectedMass_continuous)

noncomputable def clampedEvent (c : ActualEventCertificate M anchor σ) :
    C(ℝ × Stage σ, geometricRealization (actualA M)) :=
  ⟨fun z => clampedBranchingSurgeryPoint K σ c.face
    ⟨activeArcClass M c.crossing.selected.val,
      selectedActive_mem M anchor c.classes c.position c.crossing σ c.selected_mem⟩
    c.surgery.retained.attach c.surgery.nonempty.attach
    (fun b => activeArcClass M (vertex M (c.surgery.pushed b)))
    (actualSurgeryEvent_commonFace M anchor c.classes c.position c.crossing c.surgery
      σ c.face c.contains c.selected_mem)
    (z.1,fullStageFaceCoordinates K σ z.2),
    (clampedBranchingSurgeryPoint_continuous K σ c.face _ _ _ _ _).comp
      (continuous_fst.prodMk ((fullStageFaceCoordinates_continuous K σ).comp continuous_snd))⟩

theorem clampedEvent_before (c : ActualEventCertificate M anchor σ)
    (p : Stage σ) (depth : ℝ) (hd : depth ≤ 0) :
    c.clampedEvent (depth,p) = CurveComplex.fullToAmbient K (· ∈ σ) p := by
  exact (clampedBranchingSurgeryPoint_before K σ c.face
    ⟨activeArcClass M c.crossing.selected.val,
      selectedActive_mem M anchor c.classes c.position c.crossing σ c.selected_mem⟩
    c.surgery.retained.attach c.surgery.nonempty.attach
    (fun b => activeArcClass M (vertex M (c.surgery.pushed b)))
    (actualSurgeryEvent_commonFace M anchor c.classes c.position c.crossing c.surgery
      σ c.face c.contains c.selected_mem)
    (fullStageFaceCoordinates K σ p) depth hd).trans
    (faceInclusion_fullStageFaceCoordinates K σ c.face p)

theorem clampedEvent_after (c : ActualEventCertificate M anchor σ)
    (p : Stage σ) (depth : ℝ) (hd : c.selectedMass p ≤ depth) :
    c.clampedEvent (depth,p) = c.event (1,p) :=
  clampedBranchingSurgeryPoint_after K σ c.face
    ⟨activeArcClass M c.crossing.selected.val,
      selectedActive_mem M anchor c.classes c.position c.crossing σ c.selected_mem⟩
    c.surgery.retained.attach c.surgery.nonempty.attach
    (fun b => activeArcClass M (vertex M (c.surgery.pushed b)))
    (actualSurgeryEvent_commonFace M anchor c.classes c.position c.crossing c.surgery
      σ c.face c.contains c.selected_mem)
    (fullStageFaceCoordinates K σ p) depth hd

end ActualEventCertificate
namespace ActualFiniteEventTrace

/-- Number of actual cuts in the supplied geometric trace. -/
noncomputable def length : {σ : Finset (ActiveVertex (actualA M))} → ActualFiniteEventTrace M anchor σ → ℕ
  | _, .stop _ => 0
  | _, .cut _ T => T.length + 1

/-- Unnormalized durations are computed from the current actual selected mass.
The normalization of the completed cut rescales all subsequent durations. -/
noncomputable def bandWidth : {σ : Finset (ActiveVertex (actualA M))} →
    ActualFiniteEventTrace M anchor σ → ℕ → (Stage σ) → ℝ
  | _, .stop _, _, _ => 0
  | _, .cut c _, 0, p => c.selectedMass p
  | _, .cut c T, j+1, p => c.endpointScale p * T.bandWidth j (c.endpointToNext p)

noncomputable def totalWidth : {σ : Finset (ActiveVertex (actualA M))} →
    ActualFiniteEventTrace M anchor σ → (Stage σ) → ℝ
  | _, .stop _, _ => 0
  | _, .cut c T, p => c.selectedMass p + c.endpointScale p * T.totalWidth (c.endpointToNext p)

theorem bandWidth_nonneg {σ : Finset (ActiveVertex (actualA M))}
    (T : ActualFiniteEventTrace M anchor σ) : ∀ j p, 0 ≤ T.bandWidth j p := by
  induction T with
  | stop σ => intro j p; exact le_refl _
  | cut c T ih =>
    intro j p
    cases j with
    | zero => exact c.selectedMass_nonneg p
    | succ j => exact mul_nonneg (le_of_lt (c.endpointScale_positive p)) (ih j _)

theorem bandWidth_continuous {σ : Finset (ActiveVertex (actualA M))}
    (T : ActualFiniteEventTrace M anchor σ) : ∀ j, Continuous (T.bandWidth j) := by
  induction T with
  | stop σ => intro j; exact continuous_const
  | cut c T ih =>
    intro j
    cases j with
    | zero => exact c.selectedMass_continuous
    | succ j => exact c.endpointScale_continuous.mul ((ih j).comp c.endpointToNext.continuous)

theorem totalWidth_continuous {σ : Finset (ActiveVertex (actualA M))}
    (T : ActualFiniteEventTrace M anchor σ) : Continuous T.totalWidth := by
  induction T with
  | stop σ => exact continuous_const
  | cut c T ih =>
    exact c.selectedMass_continuous.add
      (c.endpointScale_continuous.mul (ih.comp c.endpointToNext.continuous))

theorem totalWidth_eq_sum {σ : Finset (ActiveVertex (actualA M))}
    (T : ActualFiniteEventTrace M anchor σ) (p : Stage σ) :
    T.totalWidth p = ∑ j ∈ Finset.range T.length, T.bandWidth j p := by
  induction T with
  | stop σ => simp [totalWidth, length]
  | cut c T ih =>
    rw [length, Finset.sum_range_succ']
    simp only [totalWidth, bandWidth, ← Finset.mul_sum, ← ih]
    ring

noncomputable def intrinsicThickness (σ : Finset (ActiveVertex (actualA M))) (p : Stage σ) : ℝ :=
  ∑ v ∈ σ, (CurveComplex.fullToAmbient K (· ∈ σ) p).weight v *
    (intersectionNumber M anchor v.val : ℝ)

theorem intrinsicThickness_nonneg (σ : Finset (ActiveVertex (actualA M))) (p : Stage σ) :
    0 ≤ intrinsicThickness (anchor := anchor) σ p :=
  Finset.sum_nonneg (fun v _ => mul_nonneg
    ((CurveComplex.fullToAmbient K (· ∈ σ) p).nonneg v) (Nat.cast_nonneg _))

theorem intrinsicThickness_continuous (σ : Finset (ActiveVertex (actualA M))) :
    Continuous (intrinsicThickness (anchor := anchor) σ) := by
  apply continuous_finsetSum
  intro v _
  exact ((CurveComplex.continuous_weight K v).comp
    (CurveComplex.fullToAmbient_continuous K (· ∈ σ))).mul continuous_const

noncomputable def intrinsicCutAmount {σ : Finset (ActiveVertex (actualA M))}
    (T : ActualFiniteEventTrace M anchor σ) (j : ℕ) (z : CurveComplex.EdgeTime × Stage σ) : ℝ :=
  min (T.bandWidth j z.2) (max 0
    (z.1.val * intrinsicThickness (anchor := anchor) σ z.2 -
      ∑ k ∈ Finset.range j, T.bandWidth k z.2))

theorem intrinsicCutAmount_continuous {σ : Finset (ActiveVertex (actualA M))}
    (T : ActualFiniteEventTrace M anchor σ) (j : ℕ) : Continuous (T.intrinsicCutAmount j) := by
  exact ((T.bandWidth_continuous j).comp continuous_snd).min
    (continuous_const.max (((continuous_subtype_val.comp continuous_fst).mul
      ((intrinsicThickness_continuous (anchor := anchor) σ).comp continuous_snd)).sub
      (continuous_finsetSum _ (fun k _ => (T.bandWidth_continuous k).comp continuous_snd))))

theorem intrinsicCutAmount_prefix_sum {σ : Finset (ActiveVertex (actualA M))}
    (T : ActualFiniteEventTrace M anchor σ) (z : CurveComplex.EdgeTime × Stage σ) :
    (∑ j ∈ Finset.range T.length, T.intrinsicCutAmount j z) =
      min (T.totalWidth z.2) (z.1.val * intrinsicThickness (anchor := anchor) σ z.2) := by
  unfold intrinsicCutAmount
  rw [bandClock_finite_prefix_sum (fun j => T.bandWidth j z.2)
    (fun j => T.bandWidth_nonneg j z.2), ← T.totalWidth_eq_sum]
  rw [max_eq_right (mul_nonneg z.1.property.1 (intrinsicThickness_nonneg _ _))]

end ActualFiniteEventTrace
end CurveComplex.HyperellipticModel.ArcSurgery
