import CurveComplexGenusTwo.Topology.ActualMain14RelativeCancellation.RawArcDiskCrosscut
import CurveComplexGenusTwo.Topology.ActualMain14RelativeCancellation.RawSelfIntrusionEnds
import RawClearanceAligned_RelativeSelectedBigonFacts
import CurveComplexGenusTwo.Topology.Smoothing.SphereAtlasProof

namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem relative_marked_bigon_first_arc_self_intrusion_crosscut
    (M : HyperellipticModel E S) (a b : NonLoopArc M)
    (B : ActualMarkedTwoSideDisk M a.toEssential b.toEssential)
    (hin : (a.image ∩ B.openInterior).Nonempty) :
    ∃ q : C(Interval,S), IsEmbedding q ∧ range q ⊆ a.image ∧
      q 0 ∈ range B.secondSide ∧ q 1 ∈ range B.secondSide ∧
      q '' Ioo (0:Interval) 1 ⊆ B.openInterior ∧
      ¬ (q 0 ∈ ({B.firstCorner,B.secondCorner}:Set S) ∧
        q 1 ∈ ({B.firstCorner,B.secondCorner}:Set S)) := by
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
  let A : C(Interval,S) := ⟨a.val.map,a.val.continuous⟩
  have hA : IsEmbedding A := (A.continuous.isClosedEmbedding a.injective).isEmbedding
  have hbranch := relative_selected_bigon_open_interior_mark_free M a.toEssential b.toEssential B
  have h0 : A 0 ∉ B.openInterior :=
    fun h => Set.disjoint_left.mp hbranch h a.val.start_marked
  have h1 : A 1 ∉ B.openInterior :=
    fun h => Set.disjoint_left.mp hbranch h a.val.end_marked
  obtain ⟨q,hq,hqa,hq0,hq1,hqin⟩ :=
    CurveComplex.LocalSurgery.raw_embedded_arc_entering_disk_has_crosscut A hA B.disk
      B.disk_embedded h0 h1 hin
  have hfree : Disjoint B.openInterior (range B.firstSide ∪ range B.secondSide) := by
    rw [← B.boundary_eq]
    apply Set.disjoint_left.mpr
    rintro x ⟨u,hu,hux⟩ ⟨v,hv,hvx⟩
    have huv := B.disk_embedded.injective (hux.trans hvx.symm)
    subst v
    have hu' : ‖u.val‖ < 1 := by
      simpa only [Set.mem_ofPred_eq,Metric.mem_ball,dist_zero_right] using hu
    have hv' : ‖u.val‖ = 1 := by
      simpa only [Set.mem_ofPred_eq,Metric.mem_sphere,dist_zero_right] using hv
    linarith
  have hqe (e : Interval) (he : q e ∈ range B.firstSide ∪ range B.secondSide) :
      q e ∈ range B.secondSide :=
    CurveComplex.LocalSurgery.raw_self_intrusion_crosscut_endpoint_on_other_side
      A B.firstSide B.secondSide q hA B.first_embedded B.first_on_curve hqa
      (B.first_zero.trans B.second_zero.symm) (B.first_one.trans B.second_one.symm)
      B.openInterior hfree hqin e he
  refine ⟨q,hq,hqa,hqe 0 (B.boundary_eq ▸ hq0),hqe 1 (B.boundary_eq ▸ hq1),hqin,?_⟩
  rintro ⟨hc0,hc1⟩
  have hcorner (x : S) (hx : x ∈ ({B.firstCorner,B.secondCorner}:Set S)) :
      x ∈ range B.firstSide := by
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · exact ⟨0,B.first_zero.trans hx.symm⟩
    · exact ⟨1,B.first_one.trans (Set.mem_singleton_iff.mp hx).symm⟩
  have hqf : range q ⊆ range B.firstSide :=
    CurveComplex.LocalSurgery.embedded_interval_subarc_subset_of_endpoints_mem
      A B.firstSide q hA hq B.first_on_curve hqa (hcorner _ hc0) (hcorner _ hc1)
  let t : Interval := ⟨1/2,by constructor <;> norm_num⟩
  have ht : t ∈ Ioo (0:Interval) 1 := by
    constructor
    · change (0:ℝ) < 1/2
      norm_num
    · change (1/2:ℝ) < 1
      norm_num
  exact Set.disjoint_left.mp hfree (hqin (Set.mem_image_of_mem q ht))
    (Or.inl (hqf (mem_range_self t)))

end CurveComplex.HyperellipticModel
