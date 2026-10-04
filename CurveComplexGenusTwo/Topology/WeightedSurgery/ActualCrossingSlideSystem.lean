import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualRelativeCrossingSlide

namespace CurveComplex.HyperellipticModel.ArcSurgery
open Set Schoenflies CurveComplex.ActualCrossingSlide
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section

def timeHomeomorph (G : AmbientIsotopy S) (t : Interval) : S ≃ₜ S :=
  Classical.choose (G.homeomorphism_at t)

theorem timeHomeomorph_apply (G : AmbientIsotopy S) (t : Interval) (p : S) :
    timeHomeomorph G t p = G.map (t,p) := Classical.choose_spec (G.homeomorphism_at t) p

def timeTransport (M : HyperellipticModel E S) (G : AmbientIsotopy S)
    (hm : ∀ t p, p ∈ M.cover.branch → G.map (t,p) = p)
    (t : Interval) (a : EssentialMarkedArc M) : EssentialMarkedArc M :=
  a.transport (timeHomeomorph G t) (fun p hp => (timeHomeomorph_apply G t p).trans (hm t p hp))

theorem timeTransport_map (M : HyperellipticModel E S) (G : AmbientIsotopy S)
    (hm : ∀ t p, p ∈ M.cover.branch → G.map (t,p) = p)
    (t : Interval) (a : EssentialMarkedArc M) (r : Interval) :
    (timeTransport M G hm t a).val.map r = G.map (t,a.val.map r) :=
  timeHomeomorph_apply G t _

theorem timeTransport_image (M : HyperellipticModel E S) (G : AmbientIsotopy S)
    (hm : ∀ t p, p ∈ M.cover.branch → G.map (t,p) = p)
    (t : Interval) (a : EssentialMarkedArc M) :
    (timeTransport M G hm t a).val.image = (fun p => G.map (t,p)) '' a.val.image := by
  change (a.val.transport (timeHomeomorph G t)
    (fun p hp => (timeHomeomorph_apply G t p).trans (hm t p hp))).image = _
  rw [MarkedArc.transport_image]
  exact congrArg (fun f : S → S => f '' a.val.image) (funext (timeHomeomorph_apply G t))

/-- One actual local slide carries the WHOLE disjoint minimum-position system,
with no new homotopy or minimum-position premise. -/
theorem actual_crossing_slide_minimum_system (M : HyperellipticModel E S)
    (anchor : EssentialMarkedArc M) (F : Finset (EssentialArcClass M))
    (hF : IsArcSimplex M F) (P : FinitePosition M anchor F)
    (U : Set S) (V : Set Plane) (hU : IsOpen U) (e : U ≃ₜ V)
    (hCV : Plane.closedSquare 0 1 ⊆ V)
    (hm : Disjoint U (M.cover.branch : Set S))
    (haxis : ∀ p : U, p.val ∈ anchor.val.image ↔ (e p).val 1 = 0)
    (a : Amount) :
    ∃ G : AmbientIsotopy S, ∃ A : Interval → {v // v ∈ F} → EssentialMarkedArc M,
      (∀ t p, p ∈ M.cover.branch → G.map (t,p) = p) ∧
      (∀ t, (fun p => G.map (t,p)) '' anchor.val.image = anchor.val.image) ∧
      (∀ t v r, (A t v).val.map r = G.map (t,(P.rep v).val.map r)) ∧
      (∀ v, Continuous (fun z : Interval × Interval => (A z.1 v).val.map z.2)) ∧
      (∀ v, (A 0 v).val.image = (P.rep v).val.image) ∧
      (∀ t v, vertex M (A t v) = v.val) ∧
      (∀ t v w, v ≠ w → Disjoint (arcInterior M (A t v)) (arcInterior M (A t w))) ∧
      (∀ t v, (crossings M anchor (A t v)).Finite) ∧
      (∀ t v, (crossings M anchor (A t v)).ncard = (crossings M anchor (P.rep v)).ncard) ∧
      (∀ t v (b : EssentialMarkedArc M), vertex M b = v.val →
        (crossings M anchor b).Finite →
        (crossings M anchor (A t v)).ncard ≤ (crossings M anchor b).ncard) := by
  classical
  let : DecidableEq (EssentialArcClass M) := instDecidableEqEssentialArcClass_arcSurgeryProducers M
  obtain ⟨K,G,hmarks,hanchor,_,_,_⟩ :=
    actual_relative_crossing_slide M anchor U V hU e hCV hm haxis a
  let A : Interval → {v // v ∈ F} → EssentialMarkedArc M :=
    fun t v => timeTransport M G hmarks t (P.rep v)
  have himage (t : Interval) : timeHomeomorph G t '' anchor.val.image = anchor.val.image := by
    exact (congrArg (fun f : S → S => f '' anchor.val.image)
      (funext (timeHomeomorph_apply G t))).trans (hanchor t)
  have hpair (v w : {v // v ∈ F}) : IsArcSimplex M {v.val,w.val} := by
    apply arcSimplex_down M _ hF
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hz | hz
    · exact hz ▸ v.property
    · exact hz ▸ w.property
  have hcount (t : Interval) (v : {v // v ∈ F}) :
      (crossings M anchor (A t v)).ncard = (crossings M anchor (P.rep v)).ncard :=
    actual_crossings_ncard_transport_preserving_anchor_image anchor (P.rep v)
      (timeHomeomorph G t) _ (himage t)
  refine ⟨G,A,hmarks,hanchor,fun t v r => timeTransport_map M G hmarks t (P.rep v) r,
    ?_,?_,?_,?_,?_,hcount,?_⟩
  · intro v
    have he : (fun z : Interval × Interval => (A z.1 v).val.map z.2) =
        (fun z => G.map (z.1,(P.rep v).val.map z.2)) := by
      funext z
      exact timeTransport_map M G hmarks z.1 (P.rep v) z.2
    rw [he]
    exact G.map.continuous.comp (continuous_fst.prodMk ((P.rep v).val.continuous.comp continuous_snd))
  · intro v
    rw [timeTransport_image]
    have he : (fun p => G.map ((0 : Interval),p)) = id := funext G.at_zero
    rw [he, Set.image_id]
  · intro t v
    have hc := marked_ambient_isotopy_prefix_preserves_class M G hmarks (P.rep v)
      (A t v) t (timeTransport_image M G hmarks t (P.rep v))
    exact hc.symm.trans (P.represents v)
  · intro t v w hvw
    exact arcInterior_transport_disjoint (P.rep v) (P.rep w) (timeHomeomorph G t) _
      (P.simplex_disjoint v w hvw (hpair v w))
  · intro t v
    change (crossings M anchor ((P.rep v).transport _ _)).Finite
    rw [actual_crossings_transport_preserving_anchor_image _ _ _ _ (himage t)]
    exact (P.finite v).image _
  · intro t v b hb hf
    rw [hcount]
    exact P.minimal v b hb hf

end
end CurveComplex.HyperellipticModel.ArcSurgery
