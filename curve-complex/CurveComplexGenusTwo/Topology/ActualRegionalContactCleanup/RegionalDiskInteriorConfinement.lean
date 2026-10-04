import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches

open CurveComplex Set Topology

theorem regional_connected_disk_interior_confined
    {S : Type} [TopologicalSpace S]
    (F : Set S) (hFclosed : IsClosed F)
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S))
    (havoid : Disjoint
      (d '' {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
      (frontier F))
    (hmeet : ∃ z : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,
      z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧ d z ∈ interior F) :
    d '' {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1} ⊆
      interior F := by
  let U : Set (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}
  have hU : IsPreconnected U := by
    have hball : IsPreconnected
        (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
      (convex_ball (0 : EuclideanSpace ℝ (Fin 2)) 1).isPreconnected
    have hsubset : Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 ⊆
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
      Metric.ball_subset_closedBall
    let e : ↥(Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) →
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
      fun z => ⟨z.val,hsubset z.property⟩
    have he : Continuous e := continuous_subtype_val.subtype_mk _
    have hrange : Set.range e = U := by
      ext z
      constructor
      · rintro ⟨w,rfl⟩
        exact w.property
      · intro hz
        exact ⟨⟨z.val,hz⟩,Subtype.ext rfl⟩
    let : PreconnectedSpace ↥(Metric.ball
        (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
      Subtype.preconnectedSpace hball
    rw [← hrange]
    simpa only [Set.image_univ] using
      (isPreconnected_univ.image e he.continuousOn)
  have hdU : IsPreconnected (d '' U) := hU.image d d.continuous.continuousOn
  have hnonempty : (d '' U ∩ interior F).Nonempty := by
    obtain ⟨z,hz,hdz⟩ := hmeet
    exact ⟨d z,⟨z,hz,rfl⟩,hdz⟩
  apply hdU.subset_of_closure_inter_subset isOpen_interior hnonempty
  intro y hy
  have hyF : y ∈ F := hFclosed.closure_eq ▸
    (closure_mono interior_subset hy.1)
  by_contra hnot
  exact Set.disjoint_left.mp havoid hy.2
    ((hFclosed.frontier_eq ▸ show y ∈ F \ interior F from ⟨hyF,hnot⟩))

theorem regional_disk_with_frontier_clear_interior_lies_in_region
    {S : Type} [TopologicalSpace S]
    (F : Set S) (hFclosed : IsClosed F)
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S))
    (hboundary : d '' {z | z.val ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} ⊆ F)
    (havoid : Disjoint
      (d '' {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
      (frontier F))
    (hmeet : ∃ z : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,
      z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧ d z ∈ interior F) :
    Set.range d ⊆ F := by
  have hinterior := regional_connected_disk_interior_confined F hFclosed d havoid hmeet
  rintro y ⟨z,rfl⟩
  by_cases hz : z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1
  · exact interior_subset (hinterior ⟨z,hz,rfl⟩)
  · have hle : dist z.val (0 : EuclideanSpace ℝ (Fin 2)) ≤ 1 := z.property
    have heq : dist z.val (0 : EuclideanSpace ℝ (Fin 2)) = 1 :=
      le_antisymm hle (le_of_not_gt (by simpa only [Metric.mem_ball] using hz))
    exact hboundary ⟨z,by simpa only [Set.mem_ofPred_eq,Metric.mem_sphere] using heq,rfl⟩

#print axioms regional_connected_disk_interior_confined
#print axioms regional_disk_with_frontier_clear_interior_lies_in_region
