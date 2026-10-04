import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches
import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.VerifiedCarrierBridgeComponents

open CurveComplex Set Topology

theorem regional_embedded_disk_interior_meets_open_region
    {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (F : Set S)
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S))
    (hd : Topology.IsEmbedding d)
    (hmeet : (Set.range d ∩ interior F).Nonempty) :
    ∃ z : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,
      z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧
      d z ∈ interior F := by
  obtain ⟨y,hyD,hyF⟩ := hmeet
  have hycl : y ∈ closure (interior (Set.range d)) := by
    rw [CurveComplex.actual_embedded_disk_closure_interior d hd]
    exact hyD
  obtain ⟨v,hvF,hvD⟩ :=
    mem_closure_iff_nhds.mp hycl (interior F) (isOpen_interior.mem_nhds hyF)
  rw [CurveComplex.LocalSurgery.embedded_surface_disk_interior_eq d hd] at hvD
  obtain ⟨z,hz,hvz⟩ := hvD
  exact ⟨z,hz,hvz ▸ hvF⟩

#print axioms regional_embedded_disk_interior_meets_open_region
