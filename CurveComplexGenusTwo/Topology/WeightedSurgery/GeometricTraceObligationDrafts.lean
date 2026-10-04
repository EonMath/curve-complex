import CurveComplexGenusTwo.Topology.WeightedSurgery.ArcSurgeryProducers
namespace CurveComplex.HyperellipticModel.ArcSurgery

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/- The source's isotopy THROUGH minimum-position systems. Endpoints match
images, because the actual quotient forgets parametrization and orientation.
No pointwise fixing of the anchor is silently required. -/
structure MinimumPositionSystemFamily (M : HyperellipticModel E S)
    (anchor : EssentialMarkedArc M) (F : Finset (EssentialArcClass M))
    (P Q : FinitePosition M anchor F) where
  arc : Interval → {v // v ∈ F} → EssentialMarkedArc M
  continuous : ∀ v, Continuous (fun z : Interval × Interval => (arc z.1 v).val.map z.2)
  starts : ∀ v, (arc 0 v).val.image = (P.rep v).val.image
  ends : ∀ v, (arc 1 v).val.image = (Q.rep v).val.image
  represents : ∀ t v, vertex M (arc t v) = v.val
  disjoint : ∀ t v w, v ≠ w → Disjoint (arcInterior M (arc t v)) (arcInterior M (arc t w))
  finite : ∀ t v, (crossings M anchor (arc t v)).Finite
  minimal : ∀ t v (b : EssentialMarkedArc M), vertex M b = v.val →
    (crossings M anchor b).Finite →
    (crossings M anchor (arc t v)).ncard ≤ (crossings M anchor b).ncard

/- Hatcher source lines101–109. Restricted to ONE actual simplex, not a
simultaneous isotopy of unrelated nonadjacent vertices of a full subcomplex. -/
abbrev AnchorCrossingParameter (M : HyperellipticModel E S)
    (anchor a : EssentialMarkedArc M) :=
  {r : Interval // 0 < r.val ∧ r.val < 1 ∧ anchor.val.map r ∈ arcInterior M a}

/- The stronger ordered geometry required by the weighted band trace.
The existing SurgeryPair only gives strict cardinal descent. That does not
identify the remaining crossings or justify the cutting depth t*theta. -/
structure OrderedSurgeryTransport (M : HyperellipticModel E S)
    (anchor : EssentialMarkedArc M) (F : Finset (EssentialArcClass M))
    (P : FinitePosition M anchor F) (x : FirstCrossing M anchor F P)
    (R : SurgeryPair M anchor F P x) where
  crossingEquiv :
    (Σ side : {side // side ∈ R.retained}, AnchorCrossingParameter M anchor (R.pushed side)) ≃
      {r : AnchorCrossingParameter M anchor (P.rep x.selected) // x.t.val < r.val.val}
  ordered : ∀ p q, p.2.val.val < q.2.val.val ↔
    (crossingEquiv p).val.val.val < (crossingEquiv q).val.val.val
  neighbor_order : ∀ p (v : {v // v ∈ F}), v ≠ x.selected →
    ∀ r : AnchorCrossingParameter M anchor (P.rep v),
      p.2.val.val < r.val.val ↔ (crossingEquiv p).val.val.val < r.val.val
  minimal : ∀ side (b : EssentialMarkedArc M), vertex M b = vertex M (R.pushed side) →
    (crossings M anchor b).Finite →
      (crossings M anchor (R.pushed side)).ncard ≤ (crossings M anchor b).ncard

/- Source ordered elimination x1,...,xm, lines137–149. Produces a surgery
certificate WITH remaining-crossing order, rather than assuming that arbitrary
push-off choices preserve it. Statement awaits source review. -/

end CurveComplex.HyperellipticModel.ArcSurgery
