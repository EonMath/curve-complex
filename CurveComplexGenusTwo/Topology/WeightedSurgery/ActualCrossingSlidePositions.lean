import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualCrossingSlideSystem
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualCrossingDiskSlide
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualCrossingChartTransport

namespace CurveComplex.HyperellipticModel.ArcSurgery
open Set Schoenflies CurveComplex.ActualCrossingSlide
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section

/-- Simultaneous ambient transport produces the entire actual finite-position
certificate, including crossing charts and distinct crossing sets. -/
def timePosition (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
    (F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
    (G : AmbientIsotopy S)
    (hm : ∀ t p, p ∈ M.cover.branch → G.map (t,p) = p)
    (ha : ∀ t, (fun p => G.map (t,p)) '' anchor.val.image = anchor.val.image)
    (t : Interval) : FinitePosition M anchor F := by
  classical
  let : DecidableEq (EssentialArcClass M) := instDecidableEqEssentialArcClass_arcSurgeryProducers M
  let h := timeHomeomorph G t
  have hmarks : ∀ p, p ∈ M.cover.branch → h p = p :=
    fun p hp => (timeHomeomorph_apply G t p).trans (hm t p hp)
  have hanchor : h '' anchor.val.image = anchor.val.image :=
    (congrArg (fun f : S → S => f '' anchor.val.image)
      (funext (timeHomeomorph_apply G t))).trans (ha t)
  have hcross (v : {v // v ∈ F}) :
      crossings M anchor (timeTransport M G hm t (P.rep v)) = h '' crossings M anchor (P.rep v) :=
    actual_crossings_transport_preserving_anchor_image anchor (P.rep v) h hmarks hanchor
  refine {
    rep := fun v => timeTransport M G hm t (P.rep v)
    represents := ?_
    simplex_disjoint := ?_
    finite := ?_
    transverse := ?_
    distinct_crossings := ?_
    minimal := ?_ }
  · intro v
    have hc := marked_ambient_isotopy_prefix_preserves_class M G hm (P.rep v)
      (timeTransport M G hm t (P.rep v)) t (timeTransport_image M G hm t (P.rep v))
    exact hc.symm.trans (P.represents v)
  · intro v w hvw hpair
    exact arcInterior_transport_disjoint (P.rep v) (P.rep w) h hmarks (P.simplex_disjoint v w hvw hpair)
  · intro v
    rw [hcross]
    exact (P.finite v).image h
  · intro v q hq
    rw [hcross] at hq
    obtain ⟨p,hp,rfl⟩ := hq
    exact actual_crossesInDisk_transport_preserving_anchor_image M anchor (P.rep v)
      h hmarks hanchor p (P.transverse v p hp)
  · intro v w hvw
    rw [hcross,hcross]
    exact (Set.disjoint_image_iff h.injective).mpr (P.distinct_crossings v w hvw)
  · intro v b hb hf
    rw [hcross, Set.ncard_image_of_injective _ h.injective]
    exact P.minimal v b hb hf

def timePositionSystem (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
    (F : Finset (EssentialArcClass M)) (hF : IsArcSimplex M F) (P : FinitePosition M anchor F)
    (G : AmbientIsotopy S)
    (hm : ∀ t p, p ∈ M.cover.branch → G.map (t,p) = p)
    (ha : ∀ t, (fun p => G.map (t,p)) '' anchor.val.image = anchor.val.image) :
    MinimumPositionSystemFamily M anchor F P (timePosition M anchor F P G hm ha 1) where
  arc t v := (timePosition M anchor F P G hm ha t).rep v
  continuous v := by
    have he : (fun z : Interval × Interval =>
        ((timePosition M anchor F P G hm ha z.1).rep v).val.map z.2) =
        (fun z => G.map (z.1,(P.rep v).val.map z.2)) := by
      funext z
      exact timeTransport_map M G hm z.1 (P.rep v) z.2
    rw [he]
    exact G.map.continuous.comp (continuous_fst.prodMk ((P.rep v).val.continuous.comp continuous_snd))
  starts v := by
    change (timeTransport M G hm 0 (P.rep v)).val.image = _
    rw [timeTransport_image]
    have he : (fun p => G.map ((0 : Interval),p)) = id := funext G.at_zero
    rw [he,Set.image_id]
  ends _ := rfl
  represents t v := (timePosition M anchor F P G hm ha t).represents v
  disjoint t v w hvw := by
    classical
    let : DecidableEq (EssentialArcClass M) := instDecidableEqEssentialArcClass_arcSurgeryProducers M
    apply (timePosition M anchor F P G hm ha t).simplex_disjoint v w hvw
    apply arcSimplex_down M _ hF
    intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with hz | hz
    · exact hz ▸ v.property
    · exact hz ▸ w.property
  finite t v := (timePosition M anchor F P G hm ha t).finite v
  minimal t v := (timePosition M anchor F P G hm ha t).minimal v

/-- An actual selected crossing and an explicit small displacement PRODUCE a
new finite minimum-position certificate and a whole-system minimum-position
family to it. The selected crossing truly moves when the displacement is nonzero. -/
theorem actual_crossing_slide_position_family (M : HyperellipticModel E S)
    (anchor : EssentialMarkedArc M) (F : Finset (EssentialArcClass M))
    (hF : IsArcSimplex M F) (P : FinitePosition M anchor F)
    (v : {v // v ∈ F}) (p : S) (hp : p ∈ crossings M anchor (P.rep v)) (a : Amount) :
    ∃ Q : FinitePosition M anchor F, ∃ G : AmbientIsotopy S,
      Nonempty (MinimumPositionSystemFamily M anchor F P Q) ∧
      (∀ t z, z ∈ M.cover.branch → G.map (t,z) = z) ∧
      (∀ t, (fun z => G.map (t,z)) '' anchor.val.image = anchor.val.image) ∧
      (∀ w, (Q.rep w).val.image = G.finalMap '' (P.rep w).val.image) ∧
      (a.val ≠ 0 → G.map (1,p) ≠ p) := by
  obtain ⟨U,V,e,hpU,K,G,hm,ha,_,_,hmove⟩ :=
    actual_crossing_disk_slide M anchor (P.rep v) p (P.transverse v p hp) a
  let Q := timePosition M anchor F P G hm ha 1
  refine ⟨Q,G,⟨timePositionSystem M anchor F hF P G hm ha⟩,hm,ha,?_,hmove⟩
  intro w
  exact timeTransport_image M G hm 1 (P.rep w)

end
end CurveComplex.HyperellipticModel.ArcSurgery
