import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.RegionalProperLineExclusion
import CurveComplexGenusTwo.Topology.ActualMain14RelativeCancellation.RawSelfIntrusionEnds
import CurveComplexGenusTwo.Topology.ActualMain14RelativeCancellation.RawArcDiskCrosscut

open CurveComplex Set Topology Schoenflies

namespace RegionalEmbeddedFamily

/-- An actual two-side disk crossed by its first original embedded arc has a
    crosscut whose ends lie on the other side. Tangent contacts are allowed. -/
theorem regional_two_side_disk_first_arc_intrusion_crosscut
    {S : Type} [TopologicalSpace S]
    [ChartedSpace Plane S] [ClosedSurface S]
    (a first second : C(Interval,S))
    (ha : Topology.IsEmbedding a)
    (hfirst : Topology.IsEmbedding first)
    (hfirstA : Set.range first ⊆ Set.range a)
    (h00 : first 0 = second 0) (h11 : first 1 = second 1)
    (d : C(Metric.closedBall (0 : Plane) 1,S))
    (hd : Topology.IsEmbedding d)
    (hboundary : d '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} =
      Set.range first ∪ Set.range second)
    (h0 : a 0 ∉ d '' {z | z.val ∈ Metric.ball (0 : Plane) 1})
    (h1 : a 1 ∉ d '' {z | z.val ∈ Metric.ball (0 : Plane) 1})
    (hin : (Set.range a ∩
      d '' {z | z.val ∈ Metric.ball (0 : Plane) 1}).Nonempty) :
    ∃ q : C(Interval,S),
      Topology.IsEmbedding q ∧
      Set.range q ⊆ Set.range a ∧
      q 0 ∈ Set.range second ∧ q 1 ∈ Set.range second ∧
      q '' Set.Ioo (0 : Interval) 1 ⊆
        d '' {z | z.val ∈ Metric.ball (0 : Plane) 1} := by
  let U := d '' {z | z.val ∈ Metric.ball (0 : Plane) 1}
  have hfree : Disjoint U (Set.range first ∪ Set.range second) := by
    rw [← hboundary]
    apply Set.disjoint_left.mpr
    rintro x ⟨u,hu,hux⟩ ⟨v,hv,hvx⟩
    have huv : u = v := hd.injective (hux.trans hvx.symm)
    subst v
    have hu' : ‖u.val‖ < 1 := by
      simpa only [Set.mem_ofPred_eq,Metric.mem_ball,dist_zero_right] using hu
    have hv' : ‖u.val‖ = 1 := by
      simpa only [Set.mem_ofPred_eq,Metric.mem_sphere,dist_zero_right] using hv
    linarith
  obtain ⟨q,hq,hqa,hq0,hq1,hqi⟩ :=
    CurveComplex.LocalSurgery.raw_embedded_arc_entering_disk_has_crosscut
      a ha d hd h0 h1 hin
  have hq0' : q 0 ∈ Set.range second :=
    CurveComplex.LocalSurgery.raw_self_intrusion_crosscut_endpoint_on_other_side
      a first second q ha hfirst hfirstA hqa h00 h11 U hfree hqi 0
      (hboundary ▸ hq0)
  have hq1' : q 1 ∈ Set.range second :=
    CurveComplex.LocalSurgery.raw_self_intrusion_crosscut_endpoint_on_other_side
      a first second q ha hfirst hfirstA hqa h00 h11 U hfree hqi 1
      (hboundary ▸ hq1)
  exact ⟨q,hq,hqa,hq0',hq1',hqi⟩

/-- An intrusion crosscut cannot have both ends at the old disk corners. -/
theorem regional_two_side_disk_first_arc_intrusion_crosscut_strict
    {S : Type} [TopologicalSpace S]
    [ChartedSpace Plane S] [ClosedSurface S]
    (a first second : C(Interval,S))
    (ha : Topology.IsEmbedding a)
    (hfirst : Topology.IsEmbedding first)
    (hfirstA : Set.range first ⊆ Set.range a)
    (h00 : first 0 = second 0) (h11 : first 1 = second 1)
    (d : C(Metric.closedBall (0 : Plane) 1,S))
    (hd : Topology.IsEmbedding d)
    (hboundary : d '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} =
      Set.range first ∪ Set.range second)
    (h0 : a 0 ∉ d '' {z | z.val ∈ Metric.ball (0 : Plane) 1})
    (h1 : a 1 ∉ d '' {z | z.val ∈ Metric.ball (0 : Plane) 1})
    (hin : (Set.range a ∩
      d '' {z | z.val ∈ Metric.ball (0 : Plane) 1}).Nonempty) :
    ∃ q : C(Interval,S),
      Topology.IsEmbedding q ∧
      Set.range q ⊆ Set.range a ∧
      q 0 ∈ Set.range second ∧ q 1 ∈ Set.range second ∧
      q '' Set.Ioo (0 : Interval) 1 ⊆
        d '' {z | z.val ∈ Metric.ball (0 : Plane) 1} ∧
      ¬ (q 0 ∈ ({first 0,first 1} : Set S) ∧
        q 1 ∈ ({first 0,first 1} : Set S)) := by
  obtain ⟨q,hq,hqa,hq0,hq1,hqi⟩ :=
    regional_two_side_disk_first_arc_intrusion_crosscut
      a first second ha hfirst hfirstA h00 h11 d hd hboundary h0 h1 hin
  refine ⟨q,hq,hqa,hq0,hq1,hqi,?_⟩
  rintro ⟨hc0,hc1⟩
  have hcorner (z : S) (hz : z ∈ ({first 0,first 1} : Set S)) :
      z ∈ Set.range first := by
    rcases Set.mem_insert_iff.mp hz with hz | hz
    · exact ⟨0,hz.symm⟩
    · exact ⟨1,(Set.mem_singleton_iff.mp hz).symm⟩
  have hqf : Set.range q ⊆ Set.range first :=
    CurveComplex.LocalSurgery.embedded_interval_subarc_subset_of_endpoints_mem
      a first q ha hq hfirstA hqa (hcorner _ hc0) (hcorner _ hc1)
  let t : Interval := ⟨1/2,by constructor <;> norm_num⟩
  have ht : t ∈ Set.Ioo (0 : Interval) 1 := by
    constructor
    · change (0 : ℝ) < 1/2
      norm_num
    · change (1/2 : ℝ) < 1
      norm_num
  have hfree : Disjoint
      (d '' {z | z.val ∈ Metric.ball (0 : Plane) 1})
      (Set.range first) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨u,hu,huz⟩ hz
    obtain ⟨v,hv,hvz⟩ := hboundary.symm ▸ (show
      z ∈ Set.range first ∪ Set.range second from Or.inl hz)
    have huv : u = v := hd.injective (huz.trans hvz.symm)
    subst v
    have hu' : ‖u.val‖ < 1 := by
      simpa only [Set.mem_ofPred_eq,Metric.mem_ball,dist_zero_right] using hu
    have hv' : ‖u.val‖ = 1 := by
      simpa only [Set.mem_ofPred_eq,Metric.mem_sphere,dist_zero_right] using hv
    linarith
  exact Set.disjoint_left.mp hfree
    (hqi (Set.mem_image_of_mem q ht)) (hqf (Set.mem_range_self t))

end RegionalEmbeddedFamily
