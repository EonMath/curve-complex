import CurveComplexGenusTwo.Topology.ActualSelectedLoopMotion.ActualSelectedLoopZeroContactTerminalSector
import CurveComplexGenusTwo.Topology.ActualSelectedLoopMotion.ActualSameClassMarkedAmbientMotion
import CurveComplexGenusTwo.Topology.ActualSelectedLoopMotion.PinchedCollarReviewRequest
import CurveComplexGenusTwo.Topology.ActualSelectedLoopMotion.ReversePinchedCollarMotion

namespace CurveComplex.HyperellipticModel

open Set Topology Schoenflies
open CurveGenusTwo.Filtration

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

private theorem pinched_strip_closed_obstacle_ambient_extension_private
    (M : HyperellipticModel E S) (P : Set S) (hP : IsClosed P)
    (base : S) (hbase : base ∈ P) (G : C(Interval × Interval, S))
    (hends : ∀ t, G (0,t) = base ∧ G (1,t) = base)
    (hinj : ∀ s t s' t', G (s,t) = G (s',t') →
      (s = s' ∧ t = t') ∨
      ((s = 0 ∨ s = 1) ∧ (s' = 0 ∨ s' = 1)))
    (havoid : ∀ s t, G (s,t) ≠ base → G (s,t) ∉ P) :
    ∃ K : AmbientIsotopy S,
      (∀ t z, z ∈ P → K.map (t,z) = z) ∧
      K.finalMap '' Set.range (fun s => G (s,1)) =
        Set.range (fun s => G (s,0)) := by
  let : T2Space S := M.sphere.symm.t2Space
  let : CompactSpace S := M.sphere.symm.compactSpace
  obtain ⟨N,hNends,hNinj,hNopen,hNavoid,hN0,hN1⟩ :=
    pinched_strip_closed_obstacle_two_sided_collar M P hP base hbase G hends hinj havoid
  obtain ⟨K,hKfix,hKimage⟩ :=
    pinched_collared_band_reverse_motion_fixes_obstacle P base N hNends hNinj hNopen hNavoid
  refine ⟨K,hKfix,?_⟩
  simpa only [hN0,hN1] using hKimage

/- The remaining relative ambient extension after the proved exact sector.
   No collar or motion is an input to this source-level leaf. -/
private theorem actual_selected_loop_zero_contact_ambient_motion_private
    (M : HyperellipticModel E S) (p : ℕ) (hp : 1 ≤ p) (T : ActualStratum M p)
    (rT : {w // w ∈ T.val} → EssentialMarkedArc M)
    (hrT : ∀ w, Quotient.mk (essentialArcSetoid M) (rT w) = w.val)
    (hdT : ∀ w z, w ≠ z → Disjoint (arcInterior M (rT w)) (arcInterior M (rT z)))
    (F J : Finset (EssentialArcClass M)) (hTF : T.val ⊆ F) (hJT : J ⊆ T.val)
    (r0 : {w // w ∈ F} → EssentialMarkedArc M)
    (hr0 : ∀ w, Quotient.mk (essentialArcSetoid M) (r0 w) = w.val)
    (hd0 : ∀ w z, w ≠ z → Disjoint (arcInterior M (r0 w)) (arcInterior M (r0 z)))
    (haligned0 : ∀ w : {w // w ∈ T.val}, w.val ∈ J →
      r0 ⟨w.val, hTF w.property⟩ = rT w)
    (r : {w // w ∈ F} → EssentialMarkedArc M)
    (hgraph : actualObjectTrace M r0 J = actualObjectTrace M r J)
    (u : {w // w ∈ T.val}) (hu : u.val ∉ J)
    (hloop : (r0 ⟨u.val,hTF u.property⟩).val.map 0 =
      (r0 ⟨u.val,hTF u.property⟩).val.map 1)
    (hzero : ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u) = ∅) :
    ∃ K : AmbientIsotopy S,
      (∀ t z, z ∈ M.cover.branch → K.map (t,z) = z) ∧
      (∀ t z, z ∈ actualObjectTrace M r J → K.map (t,z) = z) ∧
      K.finalMap '' (rT u).val.image =
        (r0 ⟨u.val,hTF u.property⟩).val.image := by
  let : T2Space S := M.sphere.symm.t2Space
  obtain ⟨e, he, G, hG0, hG1, hGends, hGinj, hGmarks, hGgraph⟩ :=
    actual_selected_loop_zero_contact_graph_relative_terminal_sector
      M p hp T rT hrT hdT F J hTF hJT r0 hr0 hd0 haligned0 r hgraph
      u hu hloop hzero
  have hclass : Quotient.mk (essentialArcSetoid M)
      (r0 ⟨u.val,hTF u.property⟩) =
      Quotient.mk (essentialArcSetoid M) (rT u) :=
    (hr0 _).trans (hrT u).symm
  obtain ⟨K0, hK0marks, hK0image⟩ :=
    actual_same_class_marked_ambient_motion
      M (r0 ⟨u.val,hTF u.property⟩) (rT u) hclass
  let P : Set S := (M.cover.branch : Set S) ∪ actualObjectTrace M r J
  let base := (r0 ⟨u.val,hTF u.property⟩).val.map 0
  have hP : IsClosed P :=
    M.cover.branch.isClosed.union (actualObjectTrace_compact M r J).isClosed
  have hbase : base ∈ P := Or.inl (r0 ⟨u.val,hTF u.property⟩).val.start_marked
  have havoid (s t : Interval) (hne : G (s,t) ≠ base) : G (s,t) ∉ P := by
    intro hmem
    rcases hmem with hmark | hgraphmem
    · by_cases hs0 : s = 0
      · exact hne (hs0 ▸ (hGends t).1)
      by_cases hs1 : s = 1
      · exact hne (hs1 ▸ (hGends t).2)
      have hs : s ∈ Set.Ioo (0 : Interval) 1 :=
        ⟨lt_of_le_of_ne s.property.1 (Ne.symm hs0),
         lt_of_le_of_ne s.property.2 hs1⟩
      exact hGmarks s t hs hmark
    · exact hGgraph s t hne hgraphmem
  obtain ⟨K,hKfix,hKimage⟩ :=
    pinched_strip_closed_obstacle_ambient_extension_private
      M P hP base hbase G hGends hGinj havoid
  refine ⟨K,?_,?_,?_⟩
  · intro t z hz
    exact hKfix t z (Or.inl hz)
  · intro t z hz
    exact hKfix t z (Or.inr hz)
  · have htop : Set.range (fun s => G (s,1)) = (rT u).val.image := by
      rw [show (fun s => G (s,1)) = (rT u).val.map ∘ e from funext hG1]
      exact e.surjective.range_comp (rT u).val.map
    have hbottom : Set.range (fun s => G (s,0)) =
        (r0 ⟨u.val,hTF u.property⟩).val.image := by
      rw [show (fun s => G (s,0)) = (r0 ⟨u.val,hTF u.property⟩).val.map
        from funext hG0]
      rfl
    simpa only [htop,hbottom] using hKimage

/-- Public visibility bridge for the identical private motion contract. -/
theorem pinched_strip_closed_obstacle_ambient_extension
    (M : HyperellipticModel E S) (P : Set S) (hP : IsClosed P)
    (base : S) (hbase : base ∈ P) (G : C(Interval × Interval, S))
    (hends : ∀ t, G (0,t) = base ∧ G (1,t) = base)
    (hinj : ∀ s t s' t', G (s,t) = G (s',t') →
      (s = s' ∧ t = t') ∨
      ((s = 0 ∨ s = 1) ∧ (s' = 0 ∨ s' = 1)))
    (havoid : ∀ s t, G (s,t) ≠ base → G (s,t) ∉ P) :
    ∃ K : AmbientIsotopy S,
      (∀ t z, z ∈ P → K.map (t,z) = z) ∧
      K.finalMap '' Set.range (fun s => G (s,1)) =
        Set.range (fun s => G (s,0)) := by
  exact pinched_strip_closed_obstacle_ambient_extension_private M P hP base hbase G hends hinj havoid

/-- Public visibility bridge for the identical private motion contract. -/
theorem actual_selected_loop_zero_contact_ambient_motion
    (M : HyperellipticModel E S) (p : ℕ) (hp : 1 ≤ p) (T : ActualStratum M p)
    (rT : {w // w ∈ T.val} → EssentialMarkedArc M)
    (hrT : ∀ w, Quotient.mk (essentialArcSetoid M) (rT w) = w.val)
    (hdT : ∀ w z, w ≠ z → Disjoint (arcInterior M (rT w)) (arcInterior M (rT z)))
    (F J : Finset (EssentialArcClass M)) (hTF : T.val ⊆ F) (hJT : J ⊆ T.val)
    (r0 : {w // w ∈ F} → EssentialMarkedArc M)
    (hr0 : ∀ w, Quotient.mk (essentialArcSetoid M) (r0 w) = w.val)
    (hd0 : ∀ w z, w ≠ z → Disjoint (arcInterior M (r0 w)) (arcInterior M (r0 z)))
    (haligned0 : ∀ w : {w // w ∈ T.val}, w.val ∈ J →
      r0 ⟨w.val, hTF w.property⟩ = rT w)
    (r : {w // w ∈ F} → EssentialMarkedArc M)
    (hgraph : actualObjectTrace M r0 J = actualObjectTrace M r J)
    (u : {w // w ∈ T.val}) (hu : u.val ∉ J)
    (hloop : (r0 ⟨u.val,hTF u.property⟩).val.map 0 =
      (r0 ⟨u.val,hTF u.property⟩).val.map 1)
    (hzero : ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u) = ∅) :
    ∃ K : AmbientIsotopy S,
      (∀ t z, z ∈ M.cover.branch → K.map (t,z) = z) ∧
      (∀ t z, z ∈ actualObjectTrace M r J → K.map (t,z) = z) ∧
      K.finalMap '' (rT u).val.image =
        (r0 ⟨u.val,hTF u.property⟩).val.image := by
  exact actual_selected_loop_zero_contact_ambient_motion_private M p hp T rT hrT hdT F J hTF hJT r0 hr0 hd0 haligned0 r hgraph u hu hloop hzero

end CurveComplex.HyperellipticModel
