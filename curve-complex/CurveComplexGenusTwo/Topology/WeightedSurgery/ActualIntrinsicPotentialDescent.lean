import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualDerivedTraceClock

namespace CurveComplex.WeightedFlowScratch
open scoped BigOperators
variable {V B : Type*} [DecidableEq V] [DecidableEq B]

/-- Actual normalized surgery conserves the explicit coefficient-weighted
numerator, including repeated replacement quotient labels. -/
theorem branchingSurgeryPoint_weighted_coefficients (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) (selected : σ)
    (branches : Finset B) (hne : branches.Nonempty) (f : B → V)
    (hnew : σ ∪ branches.image f ∈ K.faces)
    (z : EdgeTime × FiniteSimplex σ) (c : V → ℝ) :
    (∑ v ∈ σ ∪ branches.image f,
      (branchingSurgeryPoint K σ hσ selected branches hne f hnew z).weight v * c v) =
    ((∑ v ∈ σ, (faceInclusion K σ hσ z.2).weight v * c v) -
      surgeryCutMass σ selected z * c selected.val +
      surgeryCutMass σ selected z * ∑ b ∈ branches, c (f b)) /
      surgeryNormalization σ selected branches z := by
  let U := σ ∪ branches.image f
  have hold : (∑ v ∈ U, (faceInclusion K σ hσ z.2).weight v * c v) =
      ∑ v ∈ σ, (faceInclusion K σ hσ z.2).weight v * c v := by
    symm
    apply Finset.sum_subset Finset.subset_union_left
    intro v _ hv
    rw [faceInclusion_weight_of_not_mem K σ hσ z.2 v hv, zero_mul]
  have hcut : (∑ v ∈ U,
      (if v = selected.val then surgeryCutMass σ selected z else 0) * c v) =
      surgeryCutMass σ selected z * c selected.val := by
    simp only [ite_mul, zero_mul]
    simp [U, selected.property]
  have hnewsum : (∑ v ∈ U,
      (∑ b ∈ branches, if f b = v then surgeryCutMass σ selected z else 0) * c v) =
      surgeryCutMass σ selected z * ∑ b ∈ branches, c (f b) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    simp only [ite_mul, zero_mul]
    have hbU : f b ∈ U := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b,hb,rfl⟩)
    simp [hbU]
  change (∑ v ∈ U, (surgeryUnnormalizedWeight K σ hσ selected branches f z v /
    surgeryNormalization σ selected branches z) * c v) = _
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  congr 1
  simp only [surgeryUnnormalizedWeight, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, hold, hcut, hnewsum]

end CurveComplex.WeightedFlowScratch
namespace CurveComplex.HyperellipticModel.ArcSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- A supplied actual minimum-position certificate attains its intrinsic infimum. -/
theorem actual_position_count_eq_intrinsic (M : HyperellipticModel E S)
    (anchor : EssentialMarkedArc M) (F : Finset (EssentialArcClass M))
    (P : FinitePosition M anchor F) (v : {v // v ∈ F}) :
    (crossings M anchor (P.rep v)).ncard = intersectionNumber M anchor v.val := by
  apply le_antisymm
  · apply le_csInf
    · exact ⟨_, P.rep v, P.represents v, P.finite v, rfl⟩
    · rintro n ⟨b,hb,hf,rfl⟩
      exact P.minimal v b hb hf
  · exact Nat.sInf_le ⟨P.rep v, P.represents v, P.finite v, rfl⟩

/-- Any actual finite-crossing representative bounds the intrinsic count above. -/
theorem actual_intrinsic_count_le_crossings (M : HyperellipticModel E S)
    (anchor a : EssentialMarkedArc M) (hf : (crossings M anchor a).Finite) :
    intersectionNumber M anchor (vertex M a) ≤ (crossings M anchor a).ncard :=
  Nat.sInf_le ⟨a,rfl,hf,rfl⟩

open CurveGenusTwo.Filtration CurveComplex.WeightedFlowScratch
open scoped BigOperators
variable {M : HyperellipticModel E S} [LinearOrder (EssentialArcClass M)]
  {anchor : EssentialMarkedArc M}
local notation "K" => geometricComplex (actualA M)
local notation "Stage" σ => CurveComplex.RealizationPoint (CurveComplex.fullSubcomplex K (· ∈ σ))
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace ActualEventCertificate
variable {σ : Finset (ActiveVertex (actualA M))}

theorem intrinsic_coefficient_balance (c : ActualEventCertificate M anchor σ) (p : Stage σ) :
    c.endpointScale p * ActualFiniteEventTrace.intrinsicThickness (anchor := anchor)
        c.nextFace (c.endpointToNext p) =
      ActualFiniteEventTrace.intrinsicThickness (anchor := anchor) σ p -
        c.selectedMass p * (intersectionNumber M anchor c.crossing.selected.val : ℝ) +
        c.selectedMass p * ∑ b ∈ c.surgery.retained.attach,
          (intersectionNumber M anchor (vertex M (c.surgery.pushed b)) : ℝ) := by
  let U := σ ∪ c.replacementVertices
  have hsub : c.nextFace ⊆ U := Finset.union_subset
    (Finset.Subset.trans (Finset.erase_subset _ _) Finset.subset_union_left)
    Finset.subset_union_right
  have hsum : ActualFiniteEventTrace.intrinsicThickness (anchor := anchor)
        c.nextFace (c.endpointToNext p) =
      ∑ v ∈ U, (c.event (1,p)).weight v * (intersectionNumber M anchor v.val : ℝ) := by
    unfold ActualFiniteEventTrace.intrinsicThickness
    rw [c.endpointToNext_ambient]
    apply Finset.sum_subset hsub
    intro v _ hv
    rw [c.endpoint_supported p v hv, zero_mul]
  have hg := branchingSurgeryPoint_weighted_coefficients K σ c.face
    ⟨activeArcClass M c.crossing.selected.val,
      selectedActive_mem M anchor c.classes c.position c.crossing σ c.selected_mem⟩
    c.surgery.retained.attach c.surgery.nonempty.attach
    (fun b => activeArcClass M (vertex M (c.surgery.pushed b)))
    (actualSurgeryEvent_commonFace M anchor c.classes c.position c.crossing c.surgery
      σ c.face c.contains c.selected_mem)
    (1,fullStageFaceCoordinates K σ p) (fun v => (intersectionNumber M anchor v.val : ℝ))
  simp only [faceInclusion_fullStageFaceCoordinates] at hg
  have heq : ActualFiniteEventTrace.intrinsicThickness (anchor := anchor)
        c.nextFace (c.endpointToNext p) =
      (ActualFiniteEventTrace.intrinsicThickness (anchor := anchor) σ p -
        c.selectedMass p * (intersectionNumber M anchor c.crossing.selected.val : ℝ) +
        c.selectedMass p * ∑ b ∈ c.surgery.retained.attach,
          (intersectionNumber M anchor (vertex M (c.surgery.pushed b)) : ℝ)) /
        c.endpointScale p := by
    rw [hsum]
    simpa [U, replacementVertices, event, actualSurgeryFullStageEvent,
      actualSurgeryFaceEvent, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
      surgeryNormalization, surgeryCutMass, one_mul,
      fullStageFaceCoordinates, ActualFiniteEventTrace.intrinsicThickness,
      endpointScale, selectedMass, faceInclusion_fullStageFaceCoordinates,
      activeArcClass] using hg
  have hb := (eq_div_iff (ne_of_gt (c.endpointScale_positive p))).mp heq
  nlinarith

theorem intrinsic_branch_budget (c : ActualEventCertificate M anchor σ) :
    (∑ b ∈ c.surgery.retained.attach,
      (intersectionNumber M anchor (vertex M (c.surgery.pushed b)) : ℝ)) + 1 ≤
      (intersectionNumber M anchor c.crossing.selected.val : ℝ) := by
  have hs : (∑ b ∈ c.surgery.retained.attach,
      intersectionNumber M anchor (vertex M (c.surgery.pushed b))) ≤
      ∑ b ∈ c.surgery.retained.attach, (crossings M anchor (c.surgery.pushed b)).ncard :=
    Finset.sum_le_sum (fun b _ => actual_intrinsic_count_le_crossings M anchor _ (c.surgery.finite b))
  have ht := c.surgery.total_decreases
  have hc := actual_position_count_eq_intrinsic M anchor c.classes c.position c.crossing.selected
  have hn : (∑ b ∈ c.surgery.retained.attach,
      intersectionNumber M anchor (vertex M (c.surgery.pushed b))) + 1 ≤
      intersectionNumber M anchor c.crossing.selected.val := by omega
  exact_mod_cast hn

theorem intrinsic_thickness_descent (c : ActualEventCertificate M anchor σ) (p : Stage σ) :
    c.selectedMass p + c.endpointScale p * ActualFiniteEventTrace.intrinsicThickness
      (anchor := anchor) c.nextFace (c.endpointToNext p) ≤
      ActualFiniteEventTrace.intrinsicThickness (anchor := anchor) σ p := by
  have hb := c.intrinsic_coefficient_balance p
  have hbudget := mul_le_mul_of_nonneg_left c.intrinsic_branch_budget (c.selectedMass_nonneg p)
  nlinarith
end ActualEventCertificate
namespace ActualFiniteEventTrace

theorem totalWidth_le_intrinsicThickness {σ : Finset (ActiveVertex (actualA M))}
    (T : ActualFiniteEventTrace M anchor σ) : ∀ p : Stage σ,
    T.totalWidth p ≤ intrinsicThickness (anchor := anchor) σ p := by
  induction T with
  | stop σ => intro p; exact intrinsicThickness_nonneg σ p
  | cut c T ih =>
    intro p
    have htail := mul_le_mul_of_nonneg_left (ih (c.endpointToNext p))
      (le_of_lt (c.endpointScale_positive p))
    have hstep := c.intrinsic_thickness_descent p
    change c.selectedMass p + c.endpointScale p * T.totalWidth (c.endpointToNext p) ≤ _
    linarith
end ActualFiniteEventTrace

end CurveComplex.HyperellipticModel.ArcSurgery
