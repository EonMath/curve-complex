import CurveComplexGenusTwo.Topology.ActualMain14CNext.Providers.Main14ActualTwoMarkDiskUnorientedHomotopy
import CurveComplexGenusTwo.Topology.ActualMain14CNext.Providers.ActualTwoEndpointPuncturedJordan

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S] [ChartedSpace Plane E]
set_option maxHeartbeats 4000000

/-- Actual two-mark disk geometry produces a mark-free comparison region
between the ORIGINAL whole arcs when their interiors are disjoint. Neither
marked isotopy, class equality nor path homotopy is an input. -/
theorem actual_two_mark_disk_disjoint_arcs_comparison_region
    (M : HyperellipticModel E S) (a b : NonLoopArc M)
    (N : ArcNeighborhood a) (hb : b.image ⊆ interior N.closedSet)
    (hends : ({a.val.map 0,a.val.map 1}:Set S) = {b.val.map 0,b.val.map 1})
    (hmeet : a.image ∩ b.image = {a.val.map 0,a.val.map 1}) :
    ∃ Ω : Set S, Ω.Nonempty ∧ IsConnected Ω ∧ Ω ⊆ (a.image ∪ b.image)ᶜ ∧
      (∀ V : Set S, IsConnected V → Ω ⊆ V → V ⊆ (a.image ∪ b.image)ᶜ → V = Ω) ∧
      frontier Ω = a.image ∪ b.image ∧ Disjoint Ω (M.cover.branch : Set S) := by
  classical
  obtain ⟨hu,hv,α,β,hα,hβ,hhom⟩ :=
    M.actual_two_mark_disk_unoriented_arc_path_homotopy a b N hb hends
  let f : C(Interval,S) := ⟨a.val.map,a.val.continuous⟩
  let g : C(Interval,S) := ⟨fun t => (β t).val,continuous_subtype_val.comp β.continuous⟩
  have hf : IsEmbedding f := NonLoopArc.isEmbedding a
  have hgimage : range g = b.image := by
    rcases hβ with hβ | hβ
    · exact congrArg range (funext hβ)
    · exact (congrArg range (funext hβ)).trans
        (unitInterval.symmHomeomorph.surjective.range_comp _)
  have hg : IsEmbedding g := by
    rcases hβ with hβ | hβ
    · have he : (g : Interval → S) = b.val.map := funext hβ
      rw [he]; exact NonLoopArc.isEmbedding b
    · have he : (g : Interval → S) = b.val.map ∘ unitInterval.symm := funext hβ
      rw [he]; exact (NonLoopArc.isEmbedding b).comp unitInterval.symmHomeomorph.isEmbedding
  have hg0 : g 0 = a.val.map 0 := congrArg Subtype.val β.source
  have hg1 : g 1 = a.val.map 1 := congrArg Subtype.val β.target
  have hinter : range f ∩ range g = {a.val.map 0,a.val.map 1} := by
    rw [hgimage]; exact hmeet
  have hneq : a.val.map 0 ≠ a.val.map 1 := by convert a.property using 1
  obtain ⟨Ω,hn,hc,hs,hm,hfront,hfree⟩ :=
    M.actual_two_endpoint_punctured_homotopic_jordan_sides_have_empty_region f g
      (a.val.map 0) (a.val.map 1) hf hg rfl hg0 rfl hg1 hneq hinter hu hv α β hα
      (fun _ => rfl) hhom
  rw [hgimage] at hs hm hfront
  exact ⟨Ω,hn,hc,hs,hm,hfront,hfree⟩
end CurveComplex.HyperellipticModel
