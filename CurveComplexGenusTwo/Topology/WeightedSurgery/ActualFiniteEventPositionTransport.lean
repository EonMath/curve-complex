import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualAnchorRelativeTraceCompatibility
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualFiniteCrossingSlides

namespace CurveComplex.HyperellipticModel.ArcSurgery
open CurveGenusTwo.Filtration CurveComplex.WeightedFlowScratch
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
variable {M : HyperellipticModel E S} [LinearOrder (EssentialArcClass M)]
  {anchor : EssentialMarkedArc M}
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace ActualEventCertificate
variable {σ : Finset (ActiveVertex (actualA M))}

def positionTransport (c : ActualEventCertificate M anchor σ) (G : AmbientIsotopy S)
    (hm : ∀ t z, z ∈ M.cover.branch → G.map (t,z) = z)
    (ha : ∀ t, (fun z => G.map (t,z)) '' anchor.val.image = anchor.val.image)
    (u : Interval) : ActualEventCertificate M anchor σ where
  face := c.face
  classes := c.classes
  position := timePosition M anchor c.classes c.position G hm ha u
  crossing := transportFirstCrossing M anchor G hm ha c.classes c.position c.crossing u
  surgery := transportSurgeryPair M anchor G hm ha c.classes c.position c.crossing c.surgery u
  contains := c.contains
  selected_mem := c.selected_mem

theorem positionTransport_nextFace (c : ActualEventCertificate M anchor σ) (G : AmbientIsotopy S)
    (hm : ∀ t z, z ∈ M.cover.branch → G.map (t,z) = z)
    (ha : ∀ t, (fun z => G.map (t,z)) '' anchor.val.image = anchor.val.image)
    (u : Interval) : (c.positionTransport G hm ha u).nextFace = c.nextFace := by
  have he : (fun b : {b // b ∈ c.surgery.retained} =>
      activeArcClass M (vertex M (timeTransport M G hm u (c.surgery.pushed b)))) =
      (fun b => activeArcClass M (vertex M (c.surgery.pushed b))) := by
    funext b
    apply Subtype.ext
    exact (marked_ambient_isotopy_prefix_preserves_class M G hm (c.surgery.pushed b)
      (timeTransport M G hm u (c.surgery.pushed b)) u
      (timeTransport_image M G hm u (c.surgery.pushed b))).symm
  change σ.erase (activeArcClass M c.crossing.selected.val) ∪
      c.surgery.retained.attach.image (fun b => activeArcClass M (vertex M (timeTransport M G hm u (c.surgery.pushed b)))) =
    σ.erase (activeArcClass M c.crossing.selected.val) ∪
      c.surgery.retained.attach.image (fun b => activeArcClass M (vertex M (c.surgery.pushed b)))
  rw [he]

end ActualEventCertificate
namespace ActualFiniteEventTrace

/-- Execute actual position transport at EVERY surgery stage. All events and
next inputs are reconstructed from genuine transported geometry. -/
def positionTransport {σ : Finset (ActiveVertex (actualA M))}
    (T : ActualFiniteEventTrace M anchor σ) (G : AmbientIsotopy S)
    (hm : ∀ t z, z ∈ M.cover.branch → G.map (t,z) = z)
    (ha : ∀ t, (fun z => G.map (t,z)) '' anchor.val.image = anchor.val.image)
    (u : Interval) : ActualFiniteEventTrace M anchor σ :=
  match T with
  | .stop σ => .stop σ
  | .cut c tail => .cut (c.positionTransport G hm ha u)
      ((c.positionTransport_nextFace G hm ha u).symm ▸ tail.positionTransport G hm ha u)

theorem anchorRelativeGeometry_cast_right
    {σ τ κ : Finset (ActiveVertex (actualA M))}
    {T : ActualFiniteEventTrace M anchor σ} {U : ActualFiniteEventTrace M anchor τ}
    (he : τ = κ) (h : AnchorRelativeGeometry T U) : AnchorRelativeGeometry T (he ▸ U) := by
  cases he
  exact h

theorem positionTransport_geometry {σ : Finset (ActiveVertex (actualA M))}
    (T : ActualFiniteEventTrace M anchor σ) (G : AmbientIsotopy S)
    (hm : ∀ t z, z ∈ M.cover.branch → G.map (t,z) = z)
    (ha : ∀ t, (fun z => G.map (t,z)) '' anchor.val.image = anchor.val.image)
    (u : Interval) : AnchorRelativeGeometry T (T.positionTransport G hm ha u) := by
  induction T with
  | stop σ => exact AnchorRelativeGeometry.stop σ σ
  | cut c tail ih =>
    exact AnchorRelativeGeometry.cut c (c.positionTransport G hm ha u)
      tail ((c.positionTransport_nextFace G hm ha u).symm ▸ tail.positionTransport G hm ha u)
      G hm ha u rfl HEq.rfl
      (anchorRelativeGeometry_cast_right (c.positionTransport_nextFace G hm ha u).symm ih)

/-- Source intrinsic tθ homotopy is identical after the actually EXECUTED
transport, without assuming a matching homotopy or a compatibility callback. -/
theorem intrinsicHomotopy_positionTransport {σ : Finset (ActiveVertex (actualA M))}
    (T : ActualFiniteEventTrace M anchor σ) (G : AmbientIsotopy S)
    (hm : ∀ t z, z ∈ M.cover.branch → G.map (t,z) = z)
    (ha : ∀ t, (fun z => G.map (t,z)) '' anchor.val.image = anchor.val.image)
    (u : Interval)
    (p : CurveComplex.RealizationPoint (CurveComplex.fullSubcomplex (geometricComplex (actualA M)) (· ∈ σ)))
    (t : CurveComplex.EdgeTime) :
    T.intrinsicHomotopy (t,p) = (T.positionTransport G hm ha u).intrinsicHomotopy (t,p) :=
  intrinsicHomotopy_anchor_relative (T.positionTransport_geometry G hm ha u) p p rfl t

/-- Actual finite crossing-slide scripts provide the ambient transport used by
this theorem. No existence of a script to an arbitrary Q is assumed or asserted. -/
theorem intrinsicHomotopy_actual_crossing_slides
    {F : Finset (EssentialArcClass M)} {hF : IsArcSimplex M F}
    {P Q : FinitePosition M anchor F}
    (slides : ActualFiniteCrossingSlideTrace M anchor F hF P Q)
    {σ : Finset (ActiveVertex (actualA M))} (T : ActualFiniteEventTrace M anchor σ)
    (p : CurveComplex.RealizationPoint (CurveComplex.fullSubcomplex (geometricComplex (actualA M)) (· ∈ σ)))
    (t : CurveComplex.EdgeTime) :
    T.intrinsicHomotopy (t,p) =
      (T.positionTransport slides.ambient slides.ambient_marks slides.ambient_anchor_image 1).intrinsicHomotopy (t,p) :=
  T.intrinsicHomotopy_positionTransport slides.ambient slides.ambient_marks slides.ambient_anchor_image 1 p t

end ActualFiniteEventTrace
end
end CurveComplex.HyperellipticModel.ArcSurgery
