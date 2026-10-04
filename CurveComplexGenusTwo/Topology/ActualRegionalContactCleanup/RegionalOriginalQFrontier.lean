import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches

open CurveComplex Set Topology

theorem regional_original_chart_Q_frontier
    {S : Type} [TopologicalSpace S] [T2Space S]
    (e : OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin 2)))
    (center : EuclideanSpace ℝ (Fin 2))
    (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall center R ⊆ e.target) :
    frontier (e.symm '' Metric.ball center R)ᶜ =
      e.symm '' Metric.sphere center R := by
  let O : Set S := e.symm '' Metric.ball center R
  let D : Set S := e.symm '' Metric.closedBall center R
  have hO : IsOpen O := e.symm.isOpen_image_of_subset_source Metric.isOpen_ball
    (Metric.ball_subset_closedBall.trans htarget)
  have hDc : IsClosed D :=
    ((isCompact_closedBall center R).image_of_continuousOn
      (e.symm.continuousOn.mono htarget)).isClosed
  have hclosureO : closure O = D := by
    apply Set.Subset.antisymm
      (closure_minimal (Set.image_mono Metric.ball_subset_closedBall) hDc)
    have hcb : closure (Metric.ball center R) = Metric.closedBall center R :=
      closure_ball center (ne_of_gt hR)
    have hc : ContinuousOn e.symm (closure (Metric.ball center R)) := by
      rw [hcb]
      exact e.symm.continuousOn.mono htarget
    change e.symm '' Metric.closedBall center R ⊆
      closure (e.symm '' Metric.ball center R)
    rw [← hcb]
    exact hc.image_closure
  rw [frontier_compl]
  change frontier O = _
  rw [hO.frontier_eq,hclosureO]
  ext y
  constructor
  · rintro ⟨⟨v,hv,rfl⟩,hn⟩
    refine ⟨v,Metric.mem_sphere.mpr ?_,rfl⟩
    apply le_antisymm (Metric.mem_closedBall.mp hv)
    apply not_lt.mp
    intro hlt
    exact hn ⟨v,Metric.mem_ball.mpr hlt,rfl⟩
  · rintro ⟨v,hv,rfl⟩
    refine ⟨⟨v,Metric.sphere_subset_closedBall hv,rfl⟩,?_⟩
    rintro ⟨w,hw,he⟩
    have hwv : w = v := e.symm.injOn
      (htarget (Metric.ball_subset_closedBall hw))
      (htarget (Metric.sphere_subset_closedBall hv)) he
    exact (not_lt_of_ge (Metric.mem_sphere.mp hv).ge)
      (hwv ▸ Metric.mem_ball.mp hw)

#print axioms regional_original_chart_Q_frontier
