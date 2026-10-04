import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualWeightedEventPositionTransport
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualIntrinsicFiniteHomotopy

namespace CurveComplex.HyperellipticModel.ArcSurgery
open CurveGenusTwo.Filtration CurveComplex.WeightedFlowScratch
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
variable {M : HyperellipticModel E S} [LinearOrder (EssentialArcClass M)]
  {anchor : EssentialMarkedArc M}
local notation "K" => geometricComplex (actualA M)
local notation "Stage" σ => CurveComplex.RealizationPoint (CurveComplex.fullSubcomplex K (· ∈ σ))
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace ActualEventCertificate
variable {σ τ : Finset (ActiveVertex (actualA M))}

theorem event_anchor_relative_face_compatible (c : ActualEventCertificate M anchor σ)
    (d : ActualEventCertificate M anchor τ) (G : AmbientIsotopy S)
    (hm : ∀ t z, z ∈ M.cover.branch → G.map (t,z) = z)
    (ha : ∀ t, (fun z => G.map (t,z)) '' anchor.val.image = anchor.val.image)
    (u : Interval) (hc : c.classes = d.classes)
    (hP : HEq (timePosition M anchor c.classes c.position G hm ha u) d.position)
    (p : Stage σ) (q : Stage τ)
    (hpq : CurveComplex.fullToAmbient K (· ∈ σ) p = CurveComplex.fullToAmbient K (· ∈ τ) q)
    (t : CurveComplex.EdgeTime) : c.event (t,p) = d.event (t,q) := by
  cases c with
  | mk hσ Fc Pc xc Rc hFc hxc =>
    cases d with
    | mk hτ Fd Pd xd Rd hFd hxd =>
      dsimp only at hc hP
      cases hc
      cases hP
      let y := transportFirstCrossing M anchor G hm ha Fc Pc xc u
      have hxy := firstCrossing_unique M anchor Fc (timePosition M anchor Fc Pc G hm ha u) y xd
      have hsel : y.selected = xd.selected := congrArg FirstCrossing.selected hxy
      have hxσ : xd.selected.val ∈ σ.image Subtype.val := hsel ▸ hxc
      exact (actualSurgeryFullStageEvent_transported_position_choice_independent M anchor G hm ha
        Fc Pc xc Rc u xd Rd σ hσ hFc hxc hxσ (t,p)).trans
        (actualSurgeryFullStageEvent_face_compatible M anchor Fc
          (timePosition M anchor Fc Pc G hm ha u) xd Rd σ τ hσ hτ hFc hFd hxσ hxd p q hpq t)

theorem selectedMass_anchor_relative (c : ActualEventCertificate M anchor σ)
    (d : ActualEventCertificate M anchor τ) (G : AmbientIsotopy S)
    (hm : ∀ t z, z ∈ M.cover.branch → G.map (t,z) = z)
    (ha : ∀ t, (fun z => G.map (t,z)) '' anchor.val.image = anchor.val.image)
    (u : Interval) (hc : c.classes = d.classes)
    (hP : HEq (timePosition M anchor c.classes c.position G hm ha u) d.position)
    (p : Stage σ) (q : Stage τ)
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
      have hxy := firstCrossing_unique M anchor Fc (timePosition M anchor Fc Pc G hm ha u)
        (transportFirstCrossing M anchor G hm ha Fc Pc xc u) xd
      cases hxy
      exact congrArg (fun z => z.weight (activeArcClass M xc.selected.val)) hpq

theorem endpointScale_anchor_relative (c : ActualEventCertificate M anchor σ)
    (d : ActualEventCertificate M anchor τ) (G : AmbientIsotopy S)
    (hm : ∀ t z, z ∈ M.cover.branch → G.map (t,z) = z)
    (ha : ∀ t, (fun z => G.map (t,z)) '' anchor.val.image = anchor.val.image)
    (u : Interval) (hc : c.classes = d.classes)
    (hP : HEq (timePosition M anchor c.classes c.position G hm ha u) d.position)
    (p : Stage σ) (q : Stage τ)
    (hpq : CurveComplex.fullToAmbient K (· ∈ σ) p = CurveComplex.fullToAmbient K (· ∈ τ) q) :
    c.endpointScale p = d.endpointScale q := by
  have hmass := c.selectedMass_anchor_relative d G hm ha u hc hP p q hpq
  cases c with
  | mk hσ Fc Pc xc Rc hFc hxc =>
    cases d with
    | mk hτ Fd Pd xd Rd hFd hxd =>
      dsimp only at hc hP
      cases hc
      cases hP
      have hxy := firstCrossing_unique M anchor Fc (timePosition M anchor Fc Pc G hm ha u)
        (transportFirstCrossing M anchor G hm ha Fc Pc xc u) xd
      cases hxy
      have hret : Rc.retained = Rd.retained := surgeryPair_retained_independent M anchor Fc
        (timePosition M anchor Fc Pc G hm ha u)
        (transportFirstCrossing M anchor G hm ha Fc Pc xc u)
        (transportSurgeryPair M anchor G hm ha Fc Pc xc Rc u) Rd
      dsimp only [endpointScale]
      rw [hret,hmass]

theorem clampedEvent_anchor_relative_face_compatible (c : ActualEventCertificate M anchor σ)
    (d : ActualEventCertificate M anchor τ) (G : AmbientIsotopy S)
    (hm : ∀ t z, z ∈ M.cover.branch → G.map (t,z) = z)
    (ha : ∀ t, (fun z => G.map (t,z)) '' anchor.val.image = anchor.val.image)
    (u : Interval) (hc : c.classes = d.classes)
    (hP : HEq (timePosition M anchor c.classes c.position G hm ha u) d.position)
    (p : Stage σ) (q : Stage τ)
    (hpq : CurveComplex.fullToAmbient K (· ∈ σ) p = CurveComplex.fullToAmbient K (· ∈ τ) q)
    (depth : ℝ) : c.clampedEvent (depth,p) = d.clampedEvent (depth,q) := by
  have hmass := c.selectedMass_anchor_relative d G hm ha u hc hP p q hpq
  have hs : (⟨c.selectedMass p,c.selectedMass_nonneg p⟩ : {m : ℝ // 0 ≤ m}) =
      ⟨d.selectedMass q,d.selectedMass_nonneg q⟩ := Subtype.ext hmass
  have ht := congrArg (fun m : {m : ℝ // 0 ≤ m} => actualBandTime m.val m.property depth) hs
  change c.event (actualBandTime (c.selectedMass p) (c.selectedMass_nonneg p) depth,p) =
    d.event (actualBandTime (d.selectedMass q) (d.selectedMass_nonneg q) depth,q)
  rw [← ht]
  exact c.event_anchor_relative_face_compatible d G hm ha u hc hP p q hpq _
end ActualEventCertificate
namespace ActualFiniteEventTrace

/-- Geometric synchronization by actual ambient transport, rather than identical
minimum positions. This contains no map/homotopy/compatibility callback. It does
not assert existence of an arbitrary prescribed-target alignment. -/
inductive AnchorRelativeGeometry : {σ τ : Finset (ActiveVertex (actualA M))} →
    ActualFiniteEventTrace M anchor σ → ActualFiniteEventTrace M anchor τ → Prop
  | stop (σ τ) : AnchorRelativeGeometry (.stop σ) (.stop τ)
  | cut {σ τ} (c : ActualEventCertificate M anchor σ) (d : ActualEventCertificate M anchor τ)
      (T : ActualFiniteEventTrace M anchor c.nextFace) (U : ActualFiniteEventTrace M anchor d.nextFace)
      (G : AmbientIsotopy S)
      (hm : ∀ t z, z ∈ M.cover.branch → G.map (t,z) = z)
      (ha : ∀ t, (fun z => G.map (t,z)) '' anchor.val.image = anchor.val.image)
      (u : Interval) (hc : c.classes = d.classes)
      (hP : HEq (timePosition M anchor c.classes c.position G hm ha u) d.position)
      (htail : AnchorRelativeGeometry T U) : AnchorRelativeGeometry (.cut c T) (.cut d U)

theorem atDepth_anchor_relative {σ τ : Finset (ActiveVertex (actualA M))}
    {T : ActualFiniteEventTrace M anchor σ} {U : ActualFiniteEventTrace M anchor τ}
    (h : AnchorRelativeGeometry T U) : ∀ (p : Stage σ) (q : Stage τ),
    CurveComplex.fullToAmbient K (· ∈ σ) p = CurveComplex.fullToAmbient K (· ∈ τ) q →
    ∀ depth : ℝ, T.atDepth (depth,p) = U.atDepth (depth,q) := by
  induction h with
  | stop σ τ => intro p q hpq depth; exact hpq
  | cut c d T U G hm ha u hc hP htail ih =>
    intro p q hpq depth
    have hmass := c.selectedMass_anchor_relative d G hm ha u hc hP p q hpq
    have hs := c.endpointScale_anchor_relative d G hm ha u hc hP p q hpq
    simp only [atDepth]
    rw [← hmass]
    split_ifs with ht
    · exact c.clampedEvent_anchor_relative_face_compatible d G hm ha u hc hP p q hpq depth
    · rw [← hs]
      apply ih
      rw [c.endpointToNext_ambient,d.endpointToNext_ambient]
      exact c.event_anchor_relative_face_compatible d G hm ha u hc hP p q hpq 1

theorem intrinsicHomotopy_anchor_relative {σ τ : Finset (ActiveVertex (actualA M))}
    {T : ActualFiniteEventTrace M anchor σ} {U : ActualFiniteEventTrace M anchor τ}
    (h : AnchorRelativeGeometry T U) (p : Stage σ) (q : Stage τ)
    (hpq : CurveComplex.fullToAmbient K (· ∈ σ) p = CurveComplex.fullToAmbient K (· ∈ τ) q)
    (t : CurveComplex.EdgeTime) : T.intrinsicHomotopy (t,p) = U.intrinsicHomotopy (t,q) := by
  change T.atDepth (t.val * intrinsicThickness (anchor := anchor) σ p,p) =
    U.atDepth (t.val * intrinsicThickness (anchor := anchor) τ q,q)
  rw [intrinsicThickness_face_independent σ τ p q hpq]
  exact atDepth_anchor_relative h p q hpq _

end ActualFiniteEventTrace
end CurveComplex.HyperellipticModel.ArcSurgery
