import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualFirstCrossingTransport
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualRawMarkedTransport

namespace CurveComplex.HyperellipticModel.ArcSurgery
open Set
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section
variable (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
  (G : AmbientIsotopy S)
  (hm : ∀ t p, p ∈ M.cover.branch → G.map (t,p) = p)
  (ha : ∀ t, (fun p => G.map (t,p)) '' anchor.val.image = anchor.val.image)

theorem actual_spliceTrace_transport (F : Finset (EssentialArcClass M))
    (P : FinitePosition M anchor F) (x : FirstCrossing M anchor F P) (t : Interval) (side : Bool) :
    (fun p => G.map (t,p)) '' spliceTrace M anchor (P.rep x.selected) x.t x.s side =
      spliceTrace M anchor ((timePosition M anchor F P G hm ha t).rep x.selected)
        (transportFirstCrossing M anchor G hm ha F P x t).t x.s side := by
  change (fun p => G.map (t,p)) ''
    ((anchor.val.map '' {r : Interval | r.val ≤ x.t.val}) ∪
      ((P.rep x.selected).val.map '' {r : Interval | if side then x.s.val ≤ r.val else r.val ≤ x.s.val})) =
    (anchor.val.map '' {r : Interval | r.val ≤ (anchorParameterOrderIso M anchor G hm ha t x.t).val}) ∪
      ((timeTransport M G hm t (P.rep x.selected)).val.map ''
        {r : Interval | if side then x.s.val ≤ r.val else r.val ≤ x.s.val})
  rw [Set.image_union,actual_anchor_prefix_transport,Set.image_image]
  have he : (fun r => G.map (t,(P.rep x.selected).val.map r)) =
      (timeTransport M G hm t (P.rep x.selected)).val.map := by
    funext r
    exact (timeTransport_map M G hm t (P.rep x.selected) r).symm
  rw [he]

/-- Actual surgery pairs are PRODUCED in the new minimum position by ambient
transport; all raw traces, retained branches and descent certificates survive. -/
def transportSurgeryPair (F : Finset (EssentialArcClass M))
    (P : FinitePosition M anchor F) (x : FirstCrossing M anchor F P)
    (R : SurgeryPair M anchor F P x) (t : Interval) :
    SurgeryPair M anchor F (timePosition M anchor F P G hm ha t)
      (transportFirstCrossing M anchor G hm ha F P x t) := by
  classical
  let : DecidableEq (EssentialArcClass M) := instDecidableEqEssentialArcClass_arcSurgeryProducers M
  let h := timeHomeomorph G t
  have hmarks : ∀ p, p ∈ M.cover.branch → h p = p :=
    fun p hp => (timeHomeomorph_apply G t p).trans (hm t p hp)
  have hanchor : h '' anchor.val.image = anchor.val.image :=
    (congrArg (fun f : S → S => f '' anchor.val.image)
      (funext (timeHomeomorph_apply G t))).trans (ha t)
  have hcount (a : EssentialMarkedArc M) :
      (crossings M anchor (timeTransport M G hm t a)).ncard = (crossings M anchor a).ncard :=
    actual_crossings_ncard_transport_preserving_anchor_image anchor a h hmarks hanchor
  refine {
    raw := fun side => timeRawTransport M G hm t (R.raw side)
    raw_trace := ?_
    raw_start := ?_
    raw_end := ?_
    retained := R.retained
    retained_iff := ?_
    nonempty := R.nonempty
    pushed := fun side => timeTransport M G hm t (R.pushed side)
    push_isotopy := ?_
    pushed_disjoint := ?_
    disjoint_old := ?_
    disjoint_neighbors := ?_
    finite := ?_
    decreases := ?_
    total_decreases := ?_ }
  · intro side
    change ((R.raw side).transport h hmarks).image = _
    rw [MarkedArc.transport_image,R.raw_trace]
    have he := actual_spliceTrace_transport M anchor G hm ha F P x t side
    exact (congrArg (fun f : S → S => f '' spliceTrace M anchor (P.rep x.selected) x.t x.s side)
      (funext (timeHomeomorph_apply G t))).trans he
  · intro side
    rw [timeRawTransport_map,R.raw_start]
    exact hm t _ anchor.val.start_marked
  · intro side
    rw [timeRawTransport_map,R.raw_end]
    exact (timeTransport_map M G hm t (P.rep x.selected) _).symm
  · intro side
    exact (R.retained_iff side).trans (essentialMarkedArc_transport_iff M (R.raw side) h hmarks).symm
  · intro side
    let oldRaw : EssentialMarkedArc M := ⟨R.raw side.val,(R.retained_iff side.val).mp side.property⟩
    have hrawClass := marked_ambient_isotopy_prefix_preserves_class M G hm oldRaw
      (timeTransport M G hm t oldRaw) t (timeTransport_image M G hm t oldRaw)
    have hpushedClass := marked_ambient_isotopy_prefix_preserves_class M G hm (R.pushed side)
      (timeTransport M G hm t (R.pushed side)) t (timeTransport_image M G hm t (R.pushed side))
    have hraw : MarkedIsotopyRel M (R.raw side.val).image (timeRawTransport M G hm t (R.raw side.val)).image :=
      Quotient.exact hrawClass
    have hpushed : MarkedIsotopyRel M (R.pushed side).val.image
        (timeTransport M G hm t (R.pushed side)).val.image := Quotient.exact hpushedClass
    exact (markedIsotopy_equivalence M).trans ((markedIsotopy_equivalence M).symm hraw)
      ((markedIsotopy_equivalence M).trans (R.push_isotopy side) hpushed)
  · intro i j hij
    exact arcInterior_transport_disjoint (R.pushed i) (R.pushed j) h hmarks (R.pushed_disjoint i j hij)
  · intro side
    exact arcInterior_transport_disjoint (R.pushed side) (P.rep x.selected) h hmarks (R.disjoint_old side)
  · intro side v hv hpair
    exact arcInterior_transport_disjoint (R.pushed side) (P.rep v) h hmarks (R.disjoint_neighbors side v hv hpair)
  · intro side
    change (crossings M anchor ((R.pushed side).transport h hmarks)).Finite
    rw [actual_crossings_transport_preserving_anchor_image _ _ _ _ hanchor]
    exact (R.finite side).image h
  · intro side
    change (crossings M anchor (timeTransport M G hm t (R.pushed side))).ncard <
      (crossings M anchor (timeTransport M G hm t (P.rep x.selected))).ncard
    rw [hcount,hcount]
    exact R.decreases side
  · change (∑ side ∈ R.retained.attach,
      (crossings M anchor (timeTransport M G hm t (R.pushed side))).ncard) <
        (crossings M anchor (timeTransport M G hm t (P.rep x.selected))).ncard
    simp_rw [hcount]
    exact R.total_decreases

end
end CurveComplex.HyperellipticModel.ArcSurgery
