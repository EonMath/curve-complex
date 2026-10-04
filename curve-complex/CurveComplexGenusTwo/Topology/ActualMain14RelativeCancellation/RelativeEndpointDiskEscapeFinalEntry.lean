import CurveComplexGenusTwo.Topology.ActualMain14RelativeCancellation.RelativeEndpointDiskCandidate
import CurveComplexGenusTwo.Topology.ActualMain14RelativeCancellation.RawArcDiskFinalEntry
import CurveComplexGenusTwo.Topology.ActualMain14RelativeCancellation.RawSelfIntrusionEnds
import CurveComplexGenusTwo.Topology.Smoothing.SphereAtlasProof

namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- A first-arc escape followed by its actual final entry yields a crossing on
the other boundary side, with the entire terminal arc inside the candidate.
Neither the entrance point nor a returning segment is supplied. -/
theorem relative_endpoint_disk_first_arc_escape_final_entry
    (M : HyperellipticModel E S) (a b : NonLoopArc M)
    (N : ArcNeighborhood a) (C : RelativeEndpointDiskCandidate M a b N)
    (hend : a.val.map 1 ∈ C.disk ''
      {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
    (hescape : ¬ a.image ⊆ range C.disk) :
    ∃ q : C(Interval,S), IsEmbedding q ∧ range q ⊆ a.image ∧
      range q ⊆ range C.disk ∧ q 1 = a.val.map 1 ∧
      q 0 ∈ range C.secondSide ∧
      q 0 ∈ ArcSurgery.crossings M a.toEssential b.toEssential ∧
      q '' Ioc (0:Interval) 1 ⊆ C.disk ''
        {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
  classical
  let : T2Space S := M.sphere.symm.t2Space
  let : CompactSpace S := M.sphere.symm.compactSpace
  let : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    Subtype.connectedSpace (isConnected_sphere
      (by simp only [← Module.finrank_eq_rank,finrank_euclideanSpace_fin]; norm_num)
      0 (by norm_num))
  let : ConnectedSpace S := M.sphere.symm.surjective.connectedSpace M.sphere.symm.continuous
  let := (actualSphereSmoothAtlas M).charts
  let := (actualSphereSmoothAtlas M).manifold
  let : ClosedSurface S := {}
  let g : C(Interval,S) := ⟨a.val.map,a.val.continuous⟩
  have hg : IsEmbedding g := (g.continuous.isClosedEmbedding a.injective).isEmbedding
  have hout : ∃ t : Interval, g t ∉ range C.disk := by
    obtain ⟨x,hxa,hxout⟩ := Set.not_subset.mp hescape
    obtain ⟨t,rfl⟩ := hxa
    exact ⟨t,hxout⟩
  obtain ⟨r,hr1,hrb,hrin,q,hq,hqa,hqC,hq0,hq1,hqin⟩ :=
    CurveComplex.LocalSurgery.raw_embedded_arc_final_entry_segment
      g hg C.disk C.disk_embedded hend hout
  let U : Set S := C.disk ''
    {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}
  have hfree : Disjoint U (range C.firstSide ∪ range C.secondSide) := by
    rw [← C.boundary_eq]
    apply Set.disjoint_left.mpr
    rintro x ⟨u,hu,rfl⟩ ⟨v,hv,he⟩
    have huv := C.disk_embedded.injective he
    have hu' : ‖u.val‖ < 1 := by
      simpa only [Set.mem_ofPred_eq,Metric.mem_ball,dist_zero_right] using hu
    have hv' : ‖v.val‖ = 1 := by
      simpa only [Set.mem_ofPred_eq,Metric.mem_sphere,dist_zero_right] using hv
    exact (ne_of_lt hu') (huv ▸ hv')
  have hqother : q 0 ∈ range C.secondSide :=
    CurveComplex.LocalSurgery.raw_self_intrusion_crosscut_endpoint_on_other_side
      g C.firstSide C.secondSide q hg C.first_embedded C.first_on_arc hqa
      (C.first_zero.trans C.second_zero.symm) (C.first_one.trans C.second_one.symm)
      U hfree (fun x hx => hqin (Set.image_mono Ioo_subset_Ioc_self hx)) 0
      (C.boundary_eq ▸ (hq0.symm ▸ hrb))
  have hqmarkfree : q 0 ∉ M.cover.branch := by
    intro hm
    have hmr : g r ∈ M.cover.branch := hq0 ▸ hm
    rcases a.val.marked_only_at_ends r hmr with hr0 | hrone
    · obtain ⟨t,ht⟩ := hout
      have htr : t ≤ r := by
        by_contra hnot
        exact ht (Set.image_subset_range _ _ (hrin t (lt_of_not_ge hnot)))
      have htzero : t ≤ (0:Interval) := by
        change t.val ≤ 0
        change t.val ≤ r.val at htr
        have hre : r.val = 0 := congrArg Subtype.val hr0
        simpa only [hre] using htr
      have ht0 : t = 0 := le_antisymm htzero t.property.1
      have hstart : g 0 ∈ range C.disk :=
        Set.image_subset_range _ _ (C.boundary_eq.symm ▸
          (show a.val.map 0 ∈ range C.firstSide ∪ range C.secondSide from
            Or.inl ⟨0,C.first_zero⟩))
      exact ht (ht0.symm ▸ hstart)
    · exact (ne_of_lt hr1) hrone
  refine ⟨q,hq,hqa,hqC,hq1,hqother,?_,hqin⟩
  exact ⟨⟨hqa (mem_range_self 0),hqmarkfree⟩,
    C.second_on_arc hqother,hqmarkfree⟩

end CurveComplex.HyperellipticModel
