import CurveComplexGenusTwo.Topology.WeightedSurgery.ArcSurgeryProducers
import CurveComplexGenusTwo.Topology.ActualSelectedLoopStrip.SelectedLoopPinchedStripLeafRequest
import CurveComplexGenusTwo.Topology.ActualSelectedLoopStrip.ZeroContactLoopIntersection
open Lean Elab Term in
elab "checkedSelectedLoopPinchedStrip" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualSelectedLoopStrip.SelectedLoopPinchedStripLeafRequest 0).append
    `CurveComplex.HyperellipticModel.actual_selected_loop_zero_contact_prescribed_pinched_strip_leaf
  discard <| getConstInfo n
  return mkConst n
namespace CurveComplex.HyperellipticModel
open CurveGenusTwo.Filtration
open CategoryTheory
set_option maxHeartbeats 6000000
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable local instance selectedLoopTerminalSectorDecidableEqEssentialArcClass (M : HyperellipticModel E S) :
    DecidableEq (EssentialArcClass M) := Classical.decEq _
open Set Topology Schoenflies Metric Filter
open scoped Classical

theorem actual_selected_loop_zero_contact_graph_relative_terminal_sector
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
    (u : {w // w ∈ T.val}) (hu : u.val ∉ J) :
    let uF : {w // w ∈ F} := ⟨u.val, hTF u.property⟩
    let a := r0 uF
    let b := rT u
    let hclass : Quotient.mk (essentialArcSetoid M) a =
      Quotient.mk (essentialArcSetoid M) b := (hr0 uF).trans (hrT u).symm
    a.val.map 0 = a.val.map 1 → ArcSurgery.crossings M a b = ∅ →
    ∃ e : Interval ≃ₜ Interval,
      ((e 0 = 0 ∧ e 1 = 1) ∨ (e 0 = 1 ∧ e 1 = 0)) ∧
      ∃ G : C(Interval × Interval, S),
        (∀ s, G (s, 0) = a.val.map s) ∧
        (∀ s, G (s, 1) = b.val.map (e s)) ∧
        (∀ t, G (0, t) = a.val.map 0 ∧ G (1, t) = a.val.map 0) ∧
        (∀ s t s' t', G (s, t) = G (s', t') →
          (s = s' ∧ t = t') ∨
          ((s = 0 ∨ s = 1) ∧ (s' = 0 ∨ s' = 1))) ∧
        (∀ s t, s ∈ Set.Ioo (0 : Interval) 1 → G (s, t) ∉ M.cover.branch) ∧
        (∀ s t, G (s, t) ≠ a.val.map 0 →
          G (s, t) ∉ actualObjectTrace M r J) := by
  dsimp
  intro hloop hzero
  let uF : {w // w ∈ F} := ⟨u.val, hTF u.property⟩
  let a := r0 uF
  let b := rT u
  have hclass : Quotient.mk (essentialArcSetoid M) a =
      Quotient.mk (essentialArcSetoid M) b :=
    (hr0 uF).trans (hrT u).symm
  obtain ⟨U, hU, hUfree, hUfront, e, he, G, hG0, hG1,
    hGends, hGinj, hGinner, hGmarks⟩ :=
    checkedSelectedLoopPinchedStrip M a b hloop hclass hzero
  obtain ⟨V, hV, hVfree, hVfront, hVgraph⟩ :=
    actual_selected_loop_zero_contact_graph_free_between_component
      M p T rT hrT hdT F J hTF hJT r0 hr0 hd0 haligned0 r hgraph
      u hu hloop hzero
  have hUV : U = V :=
    actual_same_class_zero_contact_markfree_component_unique
      M a b hloop hclass hzero U V hU hV hUfree hVfree
  have hbound : ∀ x ∈ a.val.image ∪ b.val.image,
      x ≠ a.val.map 0 → x ∉ actualObjectTrace M r J := by
    intro x hx hne
    exact actual_selected_loop_boundaries_avoid_original_graph
      M p T rT hdT F J hTF hJT r0 hd0 haligned0 r hgraph
      u hu hloop hclass x hx hne
  refine ⟨e, he, G, hG0, hG1, hGends, hGinj, hGmarks, ?_⟩
  exact actual_pinched_strip_avoids_graph_of_graphfree_face
    M a b U V (actualObjectTrace M r J) hUV hVgraph
    (a.val.map 0) e G hG0 hG1 hGends hGinner hbound
end CurveComplex.HyperellipticModel
