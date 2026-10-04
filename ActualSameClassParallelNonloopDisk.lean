import ActualSameClassUnorientedNonloopComparison
import ActualSelectedJordanComponentDisk

namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section

/-- Source same class, nonloop and disjoint interiors PRODUCE an actual
mark-free embedded comparison disk with the ORIGINAL whole traces as its
boundary. No empty region, disk, orientation or homotopy is input. -/
theorem actual_same_class_parallel_nonloop_comparison_disk
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hclass : Quotient.mk (essentialArcSetoid M) a = Quotient.mk (essentialArcSetoid M) b)
    (ha : a.val.map 0 ≠ a.val.map 1)
    (hmeet : a.val.image ∩ b.val.image = {a.val.map 0,a.val.map 1}) :
    ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S),
      IsEmbedding d ∧
      Disjoint (d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
        (M.cover.branch : Set S) ∧
      d '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
        a.val.image ∪ b.val.image := by
  classical
  let : T2Space S := M.sphere.symm.t2Space
  obtain ⟨hu,hv,α,β,hα,hβ,hhom⟩ :=
    actual_same_class_unoriented_nonloop_path_homotopy M a b hclass ha
  let f : C(Interval,S) := ⟨a.val.map,a.val.continuous⟩
  let g : C(Interval,S) := ⟨fun t => (β t).val,continuous_subtype_val.comp β.continuous⟩
  have hgimage : range g = b.val.image := by
    rcases hβ with hβ | hβ
    · apply congrArg range; exact funext hβ
    · exact (congrArg range (funext hβ)).trans
        (unitInterval.symmHomeomorph.surjective.range_comp _)
  have hb : b.val.map 0 ≠ b.val.map 1 := by
    rcases actual_same_class_nonloop_endpoint_orientation M a b hclass ha with ⟨h0,h1⟩ | ⟨h0,h1⟩
    · simpa only [← h0,← h1] using ha
    · intro he
      exact ha (h0.trans (he.symm.trans h1.symm))
  have hf : IsEmbedding f := NonLoopArc.isEmbedding ⟨a.val,ha⟩
  have hg : IsEmbedding g := by
    rcases hβ with hβ | hβ
    · have he : (g : Interval → S) = b.val.map := funext hβ
      rw [he]; exact NonLoopArc.isEmbedding ⟨b.val,hb⟩
    · have he : (g : Interval → S) = b.val.map ∘ unitInterval.symm := funext hβ
      rw [he]
      exact (NonLoopArc.isEmbedding ⟨b.val,hb⟩).comp unitInterval.symmHomeomorph.isEmbedding
  have hg0 : g 0 = a.val.map 0 := congrArg Subtype.val β.source
  have hg1 : g 1 = a.val.map 1 := congrArg Subtype.val β.target
  have hinter : range f ∩ range g = {a.val.map 0,a.val.map 1} := by rw [hgimage]; exact hmeet
  obtain ⟨Ω,hn,hconn,hsub,hmax,hfrontier,hfree⟩ :=
    actual_two_endpoint_punctured_homotopic_jordan_sides_have_empty_region M f g
      (a.val.map 0) (a.val.map 1) hf hg rfl hg0 rfl hg1 ha hinter
      hu hv α β hα (fun _ => rfl) hhom
  have hcollision : ∀ s t : Interval, f s = g t →
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    intro s t he
    have hx : f s ∈ ({a.val.map 0,a.val.map 1} : Set S) := by
      rw [← hinter]; exact ⟨mem_range_self s,⟨t,he.symm⟩⟩
    rcases hx with hx | hx
    · exact Or.inl ⟨hf.injective hx,hg.injective (he.symm.trans (hx.trans hg0.symm))⟩
    · rw [mem_singleton_iff] at hx
      exact Or.inr ⟨hf.injective hx,hg.injective (he.symm.trans (hx.trans hg1.symm))⟩
  obtain ⟨c,hc⟩ := CurveComplex.exists_curve_of_two_arcs f g hf.injective hg.injective
    hg0.symm hg1.symm hcollision
  obtain ⟨J,hJ⟩ := actualCurve_sphereJordan M c
  let L : C(Interval,S) := ⟨M.sphere.symm ∘ J.map,M.sphere.symm.continuous.comp J.continuous⟩
  have hL : range L = range f ∪ range g := by
    change range (M.sphere.symm ∘ J.map) = _
    rw [range_comp]
    change M.sphere.symm '' J.image = _
    rw [hJ,hc,← image_comp,M.sphere.symm_comp_self,image_id]
  have hcard : ({a.val.map 0,a.val.map 1} : Finset S).card < M.cover.branch.card := by
    rw [M.cover.branch_card]
    have hle := Finset.card_insert_le (a.val.map 0) ({a.val.map 1} : Finset S)
    simp only [Finset.card_singleton] at hle
    omega
  obtain ⟨p,hpm,hpn⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hp : p ∉ range L := by
    rw [hL]
    rintro (⟨t,ht⟩ | ⟨t,ht⟩)
    · change a.val.map t = p at ht
      have htmark : a.val.map t ∈ M.cover.branch := ht.symm ▸ hpm
      rcases a.val.marked_only_at_ends t htmark with rfl | rfl
      · exact hpn (by simp [← ht])
      · exact hpn (by simp [← ht])
    · change (β t).val = p at ht
      have havoid := (β t).property
      exact havoid ⟨ht.symm ▸ hpm,by
        simpa only [Finset.mem_insert,Finset.mem_singleton,Set.mem_insert_iff,Set.mem_singleton_iff,← ht] using hpn⟩
  have hΩ : IsComplementComponent (range L) Ω := hL.symm ▸ ⟨hn,hconn,hsub,hmax⟩
  obtain ⟨d,hd,hi,hbdy⟩ := actual_selected_jordan_component_embedded_disk M L
    (congrArg M.sphere.symm J.closed)
    (fun s t he => J.injective_except_ends s t (M.sphere.symm.injective he)) p hp Ω hΩ (hL.symm ▸ hfrontier)
  refine ⟨d,hd,hi.symm ▸ hfree,?_⟩
  rw [hbdy,hL,hgimage]
  rfl
end
end CurveComplex.HyperellipticModel
