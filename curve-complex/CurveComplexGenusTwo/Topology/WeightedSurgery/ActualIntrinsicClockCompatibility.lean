import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualDepthParametrizedTrace

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
variable {σ τ : Finset (ActiveVertex (actualA M))}

theorem selectedMass_same_geometry (c : ActualEventCertificate M anchor σ)
    (d : ActualEventCertificate M anchor τ) (hc : c.classes = d.classes)
    (hP : HEq c.position d.position) (p : Stage σ) (q : Stage τ)
    (hpq : CurveComplex.fullToAmbient K (· ∈ σ) p = CurveComplex.fullToAmbient K (· ∈ τ) q) :
    c.selectedMass p = d.selectedMass q := by
  unfold selectedMass
  cases c with
  | mk hσ Fc Pc xc Rc hFc hxc =>
    cases d with
    | mk hτ Fd Pd xd Rd hFd hxd =>
      dsimp only at hc hP
      cases hc
      cases hP
      have hcross := firstCrossing_unique M anchor Fc Pc xc xd
      cases hcross
      exact congrArg (fun u => u.weight (activeArcClass M xc.selected.val)) hpq

theorem endpointScale_same_geometry (c : ActualEventCertificate M anchor σ)
    (d : ActualEventCertificate M anchor τ) (hc : c.classes = d.classes)
    (hP : HEq c.position d.position) (p : Stage σ) (q : Stage τ)
    (hpq : CurveComplex.fullToAmbient K (· ∈ σ) p = CurveComplex.fullToAmbient K (· ∈ τ) q) :
    c.endpointScale p = d.endpointScale q := by
  have hm := c.selectedMass_same_geometry d hc hP p q hpq
  cases c with
  | mk hσ Fc Pc xc Rc hFc hxc =>
    cases d with
    | mk hτ Fd Pd xd Rd hFd hxd =>
      dsimp only at hc hP
      cases hc
      cases hP
      have hcross := firstCrossing_unique M anchor Fc Pc xc xd
      cases hcross
      dsimp only [endpointScale]
      rw [surgeryPair_retained_independent M anchor Fc Pc xc Rc Rd, hm]

theorem clampedEvent_same_geometry_face_compatible (c : ActualEventCertificate M anchor σ)
    (d : ActualEventCertificate M anchor τ) (hc : c.classes = d.classes)
    (hP : HEq c.position d.position) (p : Stage σ) (q : Stage τ)
    (hpq : CurveComplex.fullToAmbient K (· ∈ σ) p = CurveComplex.fullToAmbient K (· ∈ τ) q)
    (depth : ℝ) : c.clampedEvent (depth,p) = d.clampedEvent (depth,q) := by
  have hm := c.selectedMass_same_geometry d hc hP p q hpq
  have hs : (⟨c.selectedMass p,c.selectedMass_nonneg p⟩ : {m : ℝ // 0 ≤ m}) =
      ⟨d.selectedMass q,d.selectedMass_nonneg q⟩ := Subtype.ext hm
  have ht := congrArg (fun m : {m : ℝ // 0 ≤ m} => actualBandTime m.val m.property depth) hs
  change c.event (actualBandTime (c.selectedMass p) (c.selectedMass_nonneg p) depth,p) =
    d.event (actualBandTime (d.selectedMass q) (d.selectedMass_nonneg q) depth,q)
  rw [← ht]
  exact c.event_same_geometry_face_compatible d hc hP p q hpq _
end ActualEventCertificate
namespace ActualFiniteEventTrace

theorem intrinsicThickness_face_independent (σ τ : Finset (ActiveVertex (actualA M)))
    (p : Stage σ) (q : Stage τ)
    (hpq : CurveComplex.fullToAmbient K (· ∈ σ) p = CurveComplex.fullToAmbient K (· ∈ τ) q) :
    intrinsicThickness (anchor := anchor) σ p = intrinsicThickness (anchor := anchor) τ q := by
  unfold intrinsicThickness
  have hl : (∑ v ∈ σ, (CurveComplex.fullToAmbient K (· ∈ σ) p).weight v *
      (intersectionNumber M anchor v.val : ℝ)) =
      ∑ v ∈ σ ∪ τ, (CurveComplex.fullToAmbient K (· ∈ σ) p).weight v *
        (intersectionNumber M anchor v.val : ℝ) := by
    apply Finset.sum_subset Finset.subset_union_left
    intro v _ hv
    rw [CurveComplex.fullToAmbient_weight_of_not_property K (· ∈ σ) p v hv, zero_mul]
  have hr : (∑ v ∈ τ, (CurveComplex.fullToAmbient K (· ∈ τ) q).weight v *
      (intersectionNumber M anchor v.val : ℝ)) =
      ∑ v ∈ σ ∪ τ, (CurveComplex.fullToAmbient K (· ∈ τ) q).weight v *
        (intersectionNumber M anchor v.val : ℝ) := by
    apply Finset.sum_subset Finset.subset_union_right
    intro v _ hv
    rw [CurveComplex.fullToAmbient_weight_of_not_property K (· ∈ τ) q v hv, zero_mul]
  rw [hl,hr,hpq]

theorem atDepth_face_independent {σ τ : Finset (ActiveVertex (actualA M))}
    {T : ActualFiniteEventTrace M anchor σ} {U : ActualFiniteEventTrace M anchor τ}
    (h : SameGeometry T U) : ∀ (p : Stage σ) (q : Stage τ),
    CurveComplex.fullToAmbient K (· ∈ σ) p = CurveComplex.fullToAmbient K (· ∈ τ) q →
    ∀ depth : ℝ, T.atDepth (depth,p) = U.atDepth (depth,q) := by
  induction h with
  | stop σ τ => intro p q hpq depth; exact hpq
  | cut c d T U hc hP htail ih =>
    intro p q hpq depth
    have hm := c.selectedMass_same_geometry d hc hP p q hpq
    have hs := c.endpointScale_same_geometry d hc hP p q hpq
    simp only [atDepth]
    rw [← hm]
    split_ifs with ht
    · exact c.clampedEvent_same_geometry_face_compatible d hc hP p q hpq depth
    · rw [← hs]
      apply ih
      rw [c.endpointToNext_ambient, d.endpointToNext_ambient]
      exact c.event_same_geometry_face_compatible d hc hP p q hpq 1

theorem intrinsicDepthMap_face_independent {σ τ : Finset (ActiveVertex (actualA M))}
    {T : ActualFiniteEventTrace M anchor σ} {U : ActualFiniteEventTrace M anchor τ}
    (h : SameGeometry T U) (p : Stage σ) (q : Stage τ)
    (hpq : CurveComplex.fullToAmbient K (· ∈ σ) p = CurveComplex.fullToAmbient K (· ∈ τ) q)
    (t : CurveComplex.EdgeTime) : T.intrinsicDepthMap (t,p) = U.intrinsicDepthMap (t,q) := by
  change T.atDepth (t.val * intrinsicThickness (anchor := anchor) σ p,p) =
    U.atDepth (t.val * intrinsicThickness (anchor := anchor) τ q,q)
  rw [← intrinsicThickness_face_independent σ τ p q hpq]
  exact atDepth_face_independent h p q hpq _

end ActualFiniteEventTrace
end CurveComplex.HyperellipticModel.ArcSurgery
