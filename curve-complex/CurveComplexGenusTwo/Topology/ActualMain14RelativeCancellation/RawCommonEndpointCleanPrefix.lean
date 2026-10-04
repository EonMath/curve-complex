import CurveComplexGenusTwo.Topology.ActualMain14RelativeCancellation.RawArcSubarcOpen

namespace CurveComplex.LocalSurgery
open Set Topology

theorem embedded_interval_range_contains_between
    {S : Type} [TopologicalSpace S] (a f : C(Interval,S))
    (ha : IsEmbedding a) (hfa : range f ⊆ range a)
    (u v t : Interval) (hu : a u ∈ range f) (hv : a v ∈ range f)
    (ht : t ∈ Icc u v) : a t ∈ range f := by
  let e : Interval ≃ₜ range a := ha.toHomeomorph
  let cf : Interval → Interval := fun t => e.symm ⟨f t,hfa (mem_range_self t)⟩
  have hcf : Continuous cf := e.symm.continuous.comp (f.continuous.subtype_mk _)
  have hfm (t : Interval) : a (cf t) = f t :=
    congrArg Subtype.val (e.apply_symm_apply ⟨f t,hfa (mem_range_self t)⟩)
  have hin (w : Interval) (hw : a w ∈ range f) : w ∈ range cf := by
    obtain ⟨s,hs⟩ := hw
    exact ⟨s,ha.injective ((hfm s).trans hs)⟩
  have hconn : IsPreconnected (range cf) := by
    simpa only [Set.image_univ] using isPreconnected_univ.image cf hcf.continuousOn
  obtain ⟨s,hs⟩ := hconn.Icc_subset (hin u hu) (hin v hv) ht
  exact ⟨s,(hfm s).symm.trans (congrArg a hs)⟩

/-- A common-endpoint prefix with no contacts with the entire second trace
except its endpoints is contained in every returning prefix that reaches that
trace. This compares actual embedded intervals, not chosen source parameters. -/
theorem clean_common_endpoint_prefix_subset_returning_prefix
    {S : Type} [TopologicalSpace S]
    (a f q : C(Interval,S)) (ha : IsEmbedding a) (hf : IsEmbedding f)
    (hfa : range f ⊆ range a) (hqa : range q ⊆ range a)
    (hf0 : f 0 = a 0) (hq0 : a 0 ∈ range q)
    (G : Set S) (hclean : range f ∩ G = {a 0,f 1})
    (u : Interval) (hu : a u ∈ range q) (huG : a u ∈ G)
    (hu0 : u ≠ 0) : range f ⊆ range q := by
  obtain ⟨v,hv⟩ := hfa (mem_range_self 1)
  have hv0 : v ≠ 0 := by
    intro he
    have hf10 : f 1 = f 0 := hv.symm.trans ((congrArg a he).trans hf0.symm)
    have honezero := hf.injective hf10
    norm_num at honezero
  have hvu : v ≤ u := by
    by_contra hnot
    have huF : a u ∈ range f := embedded_interval_range_contains_between
      a f ha hfa 0 v u ⟨0,hf0⟩ ⟨1,hv.symm⟩ ⟨u.property.1,le_of_lt (lt_of_not_ge hnot)⟩
    have he : a u ∈ ({a 0,f 1}:Set S) := hclean ▸ ⟨huF,huG⟩
    rcases mem_insert_iff.mp he with he | he
    · exact hu0 (ha.injective he)
    · have huv : u = v := ha.injective ((mem_singleton_iff.mp he).trans hv.symm)
      exact hnot (huv.symm ▸ le_rfl)
  have hf1q : f 1 ∈ range q := hv ▸
    embedded_interval_range_contains_between a q ha hqa 0 u v hq0 hu
      ⟨v.property.1,hvu⟩
  exact embedded_interval_subarc_subset_of_endpoints_mem a q f ha hf hqa hfa
    (hf0.symm ▸ hq0) hf1q

end CurveComplex.LocalSurgery
