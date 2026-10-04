import CurveComplexGenusTwo.Topology.ActualMain14RelativeCancellation.RawArcSubarcOpen

namespace CurveComplex.LocalSurgery
open Set Topology

/-- A crosscut following one original embedded interval cannot leave its own
disk-boundary side through a non-corner of that side. -/
theorem raw_self_intrusion_crosscut_endpoint_on_other_side
    {S : Type} [TopologicalSpace S]
    (a f g q : C(Interval,S)) (ha : IsEmbedding a) (hf : IsEmbedding f)
    (hfa : range f ⊆ range a) (hqa : range q ⊆ range a)
    (hf0 : f 0 = g 0) (hf1 : f 1 = g 1)
    (U : Set S) (hfree : Disjoint U (range f ∪ range g))
    (hqin : q '' Ioo (0:Interval) 1 ⊆ U)
    (e : Interval) (hqe : q e ∈ range f ∪ range g) : q e ∈ range g := by
  by_contra hnot
  have hefirst : q e ∈ range f := hqe.resolve_right hnot
  obtain ⟨v,hv⟩ := hefirst
  have hv0 : v ≠ 0 := by
    intro h
    exact hnot ⟨0,hf0.symm.trans ((congrArg f h).symm.trans hv)⟩
  have hv1 : v ≠ 1 := by
    intro h
    exact hnot ⟨1,hf1.symm.trans ((congrArg f h).symm.trans hv)⟩
  have hvI : v ∈ Ioo (0:Interval) 1 :=
    ⟨lt_of_le_of_ne v.property.1 (Ne.symm hv0),lt_of_le_of_ne v.property.2 hv1⟩
  let qa : C(Interval,range a) := ⟨fun t => ⟨q t,hqa (mem_range_self t)⟩,
    q.continuous.subtype_mk _⟩
  let V : Set Interval := qa ⁻¹' {x : range a | (x:S) ∈ f '' Ioo (0:Interval) 1}
  have hVo : IsOpen V := (embedded_interval_subarc_interior_isOpen a f ha hf hfa).preimage
    qa.continuous
  have heV : e ∈ V := ⟨v,hvI,hv⟩
  have hecl : e ∈ closure (Ioo (0:Interval) 1) := by
    rw [closure_Ioo (by norm_num : (0:Interval) ≠ 1)]
    exact e.property
  obtain ⟨t,htV,htI⟩ := mem_closure_iff_nhds.mp hecl V (hVo.mem_nhds heV)
  have htU : q t ∈ U := hqin (mem_image_of_mem q htI)
  obtain ⟨w,hwI,hw⟩ := htV
  exact Set.disjoint_left.mp hfree htU (Or.inl ⟨w,hw⟩)

end CurveComplex.LocalSurgery
