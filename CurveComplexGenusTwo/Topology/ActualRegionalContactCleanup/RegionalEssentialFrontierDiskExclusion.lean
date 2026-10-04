import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalDiskInteriorConfinement
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalNullBigon

open CurveComplex Set Topology

theorem regional_essential_frontier_disk_confined
    {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (F B : Set S) (hFclosed : IsClosed F)
    (J : Type) [Fintype J] (c : J → EssentialCurve S)
    (hfrontier : frontier F = B ∪ ⋃ i, (c i).val.image)
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S))
    (hd : Topology.IsEmbedding d)
    (hboundary : d '' {z | z.val ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} ⊆ F)
    (hboundaryClear : ∀ i, Disjoint (c i).val.image
      (d '' {z | z.val ∈ Metric.sphere
        (0 : EuclideanSpace ℝ (Fin 2)) 1}))
    (hinteriorB : Disjoint
      (d '' {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}) B)
    (hmeet : ∃ z : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,
      z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧ d z ∈ interior F) :
    Set.range d ⊆ F := by
  have hcurves : ∀ i, Disjoint (c i).val.image (Set.range d) := by
    intro i
    exact RegionalEmbeddedFamily.essential_curve_avoids_disk_of_boundary_disjoint
      (c i) d hd (hboundaryClear i)
  have havoid : Disjoint
      (d '' {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
      (frontier F) := by
    apply Set.disjoint_left.mpr
    intro y hy hyfront
    rw [hfrontier] at hyfront
    rcases hyfront with hyB | hyG
    · exact Set.disjoint_left.mp hinteriorB hy hyB
    · obtain ⟨i,hyi⟩ := Set.mem_iUnion.mp hyG
      exact Set.disjoint_left.mp (hcurves i) hyi
        (Set.image_subset_range _ _ hy)
  exact regional_disk_with_frontier_clear_interior_lies_in_region
    F hFclosed d hboundary havoid hmeet

#print axioms regional_essential_frontier_disk_confined
