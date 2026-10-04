import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualCrossingSlidePositions
import CurveComplexGenusTwo.Topology.Smoothing.FiniteIsotopyAssembly

namespace CurveComplex.HyperellipticModel.ArcSurgery
open Set Schoenflies CurveComplex.ActualCrossingSlide
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section

structure ActualCrossingSlideResult (M : HyperellipticModel E S)
    (anchor : EssentialMarkedArc M) (F : Finset (EssentialArcClass M))
    (P : FinitePosition M anchor F) (p : S) (a : Amount) where
  next : FinitePosition M anchor F
  ambient : AmbientIsotopy S
  system : MinimumPositionSystemFamily M anchor F P next
  marks : ∀ t z, z ∈ M.cover.branch → ambient.map (t,z) = z
  anchor_image : ∀ t, (fun z => ambient.map (t,z)) '' anchor.val.image = anchor.val.image
  endpoint_image : ∀ v, (next.rep v).val.image = ambient.finalMap '' (P.rep v).val.image
  moves_crossing : a.val ≠ 0 → ambient.map (1,p) ≠ p

/-- All fields come from the explicit actual crossing-slide producer. -/
def produceActualCrossingSlide (M : HyperellipticModel E S)
    (anchor : EssentialMarkedArc M) (F : Finset (EssentialArcClass M))
    (hF : IsArcSimplex M F) (P : FinitePosition M anchor F)
    (v : {v // v ∈ F}) (p : S) (hp : p ∈ crossings M anchor (P.rep v)) (a : Amount) :
    ActualCrossingSlideResult M anchor F P p a := by
  have hn : Nonempty (ActualCrossingSlideResult M anchor F P p a) := by
    obtain ⟨Q,G,hH,hm,ha,he,hmove⟩ := actual_crossing_slide_position_family M anchor F hF P v p hp a
    exact ⟨⟨Q,G,Classical.choice hH,hm,ha,he,hmove⟩⟩
  exact Classical.choice hn

/-- A finite script of actual crossings and displacements. Each next position
is PRODUCED by the local slide; there are no supplied isotopy/matching fields. -/
inductive ActualFiniteCrossingSlideTrace (M : HyperellipticModel E S)
    (anchor : EssentialMarkedArc M) (F : Finset (EssentialArcClass M))
    (hF : IsArcSimplex M F) : FinitePosition M anchor F → FinitePosition M anchor F → Type
  | stop (P) : ActualFiniteCrossingSlideTrace M anchor F hF P P
  | cut (P : FinitePosition M anchor F) (v : {v // v ∈ F}) (p : S)
      (hp : p ∈ crossings M anchor (P.rep v)) (a : Amount)
      {Q : FinitePosition M anchor F}
      (tail : ActualFiniteCrossingSlideTrace M anchor F hF
        (produceActualCrossingSlide M anchor F hF P v p hp a).next Q) :
      ActualFiniteCrossingSlideTrace M anchor F hF P Q

namespace ActualFiniteCrossingSlideTrace
variable {M : HyperellipticModel E S} {anchor : EssentialMarkedArc M}
  {F : Finset (EssentialArcClass M)} {hF : IsArcSimplex M F}

/-- All-time composition of the actual moves avoids artificial intermediate
positions: every factor preserves the anchor image and exact cardinalities. -/
def ambient {P Q : FinitePosition M anchor F} :
    ActualFiniteCrossingSlideTrace M anchor F hF P Q → AmbientIsotopy S
  | .stop _ => AmbientIsotopy.identity S
  | .cut P v p hp a tail =>
      (produceActualCrossingSlide M anchor F hF P v p hp a).ambient.compose tail.ambient

theorem ambient_marks {P Q : FinitePosition M anchor F}
    (T : ActualFiniteCrossingSlideTrace M anchor F hF P Q) :
    ∀ t z, z ∈ M.cover.branch → T.ambient.map (t,z) = z := by
  induction T with
  | stop P => intro t z hz; rfl
  | cut P v p hp a tail ih =>
    intro t z hz
    change tail.ambient.map (t,(produceActualCrossingSlide M anchor F hF P v p hp a).ambient.map (t,z)) = z
    rw [(produceActualCrossingSlide M anchor F hF P v p hp a).marks t z hz]
    exact ih t z hz

theorem ambient_anchor_image {P Q : FinitePosition M anchor F}
    (T : ActualFiniteCrossingSlideTrace M anchor F hF P Q) :
    ∀ t, (fun z => T.ambient.map (t,z)) '' anchor.val.image = anchor.val.image := by
  induction T with
  | stop P => intro t; exact Set.image_id _
  | cut P v p hp a tail ih =>
    intro t
    change (fun z => tail.ambient.map (t,(produceActualCrossingSlide M anchor F hF P v p hp a).ambient.map (t,z))) '' _ = _
    calc
      _ = (fun z => tail.ambient.map (t,z)) ''
          ((fun z => (produceActualCrossingSlide M anchor F hF P v p hp a).ambient.map (t,z)) '' anchor.val.image) :=
        (Set.image_image _ _ _).symm
      _ = anchor.val.image := by
        rw [(produceActualCrossingSlide M anchor F hF P v p hp a).anchor_image t, ih t]

theorem endpoint_image {P Q : FinitePosition M anchor F}
    (T : ActualFiniteCrossingSlideTrace M anchor F hF P Q) :
    ∀ v, (Q.rep v).val.image = T.ambient.finalMap '' (P.rep v).val.image := by
  induction T with
  | stop P => intro v; exact (Set.image_id _).symm
  | cut P v p hp a tail ih =>
    intro w
    rw [ih w, (produceActualCrossingSlide M anchor F hF P v p hp a).endpoint_image w,
      Set.image_image]
    rfl

/-- Finite iteration produces a genuine minimum-position system family for the
actual output positions of the script. Arbitrary target alignment is not assumed. -/
def system {P Q : FinitePosition M anchor F}
    (T : ActualFiniteCrossingSlideTrace M anchor F hF P Q) :
    MinimumPositionSystemFamily M anchor F P Q := by
  let H := timePositionSystem M anchor F hF P T.ambient T.ambient_marks T.ambient_anchor_image
  exact {
    arc := H.arc
    continuous := H.continuous
    starts := H.starts
    ends := fun v => (timeTransport_image M T.ambient T.ambient_marks 1 (P.rep v)).trans
      (T.endpoint_image v).symm
    represents := H.represents
    disjoint := H.disjoint
    finite := H.finite
    minimal := H.minimal }

end ActualFiniteCrossingSlideTrace
end
end CurveComplex.HyperellipticModel.ArcSurgery
