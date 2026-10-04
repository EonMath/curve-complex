import CurveComplexGenusTwo.Topology.ActualMain14RelativeCancellation.RelativeFirstContactDiskCandidate
import CurveComplexGenusTwo.Topology.ActualMain14RelativeCancellation.RawArcDiskFinalEntry
import CurveComplexGenusTwo.Topology.ActualMain14RelativeCancellation.RawSelfIntrusionEnds
import CurveComplexGenusTwo.Topology.ActualMain14RelativeCancellation.RawCommonEndpointCleanPrefix
import CurveComplexGenusTwo.Topology.Smoothing.SphereAtlasProof

namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- An actual first-contact endpoint disk containing the other endpoint must
contain the entire second arc: any final return would hit its clean first side
at a corner, and the preceding whole second-arc prefix is already boundary. -/
theorem relative_clean_first_side_endpoint_disk_contains_second_arc
    (M : HyperellipticModel E S) (a b : NonLoopArc M)
    (N : ArcNeighborhood a) (C : RelativeEndpointDiskCandidate M a b N)
    (hstart : b.val.map 0 = a.val.map 0)
    (hclean : range C.firstSide ∩ b.image = {a.val.map 0,C.contact})
    (hend : b.val.map 1 ∈ C.disk ''
      {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}) :
    b.image ⊆ range C.disk := by
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
  by_contra hescape
  let g : C(Interval,S) := ⟨b.val.map,b.val.continuous⟩
  have hg : IsEmbedding g := (g.continuous.isClosedEmbedding b.injective).isEmbedding
  obtain ⟨x,hxb,hxout⟩ := Set.not_subset.mp hescape
  obtain ⟨t,rfl⟩ := hxb
  obtain ⟨r,hr1,hrb,hrin,q,hq,hqa,hqC,hq0,hq1,hqin⟩ :=
    CurveComplex.LocalSurgery.raw_embedded_arc_final_entry_segment
      g hg C.disk C.disk_embedded hend ⟨t,hxout⟩
  let U : Set S := C.disk ''
    {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}
  have hfree : Disjoint U (range C.secondSide ∪ range C.firstSide) := by
    rw [Set.union_comm,← C.boundary_eq]
    apply Set.disjoint_left.mpr
    rintro x ⟨u,hu,rfl⟩ ⟨v,hv,he⟩
    have huv := C.disk_embedded.injective he
    have hu' : ‖u.val‖ < 1 := by
      simpa only [Set.mem_ofPred_eq,Metric.mem_ball,dist_zero_right] using hu
    have hv' : ‖v.val‖ = 1 := by
      simpa only [Set.mem_ofPred_eq,Metric.mem_sphere,dist_zero_right] using hv
    exact (ne_of_lt hu') (huv ▸ hv')
  have hqfirst : q 0 ∈ range C.firstSide :=
    CurveComplex.LocalSurgery.raw_self_intrusion_crosscut_endpoint_on_other_side
      g C.secondSide C.firstSide q hg C.second_embedded C.second_on_arc hqa
      (C.second_zero.trans C.first_zero.symm) (C.second_one.trans C.first_one.symm)
      U hfree (fun x hx => hqin (Set.image_mono Ioo_subset_Ioc_self hx)) 0
      (Set.union_comm _ _ ▸ (C.boundary_eq ▸ (hq0.symm ▸ hrb)))
  have hcorner : q 0 ∈ ({a.val.map 0,C.contact}:Set S) :=
    hclean ▸ ⟨hqfirst,hqa (mem_range_self 0)⟩
  have hqsecond : q 0 ∈ range C.secondSide := by
    rcases mem_insert_iff.mp hcorner with he | he
    · exact ⟨0,C.second_zero.trans he.symm⟩
    · exact ⟨1,C.second_one.trans (mem_singleton_iff.mp he).symm⟩
  have htr : t ≤ r := by
    by_contra hnot
    exact hxout (Set.image_subset_range _ _ (hrin t (lt_of_not_ge hnot)))
  have htb : g t ∈ range C.secondSide :=
    CurveComplex.LocalSurgery.embedded_interval_range_contains_between
      g C.secondSide hg C.second_on_arc 0 r t
      ⟨0,C.second_zero.trans hstart.symm⟩ (hq0 ▸ hqsecond) ⟨t.property.1,htr⟩
  apply hxout
  have hboundary : g t ∈ C.disk ''
      {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} :=
    C.boundary_eq.symm ▸ (show g t ∈ range C.firstSide ∪ range C.secondSide from Or.inr htb)
  exact Set.image_subset_range _ _ hboundary

end CurveComplex.HyperellipticModel
