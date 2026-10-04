import CurveComplexGenusTwo.Topology.IntersectionParity.SurfaceDiskInterior
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches

open CurveComplex Set Topology

theorem regional_embedded_subregion_disk_interior_avoids_boundary
    {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (Q B : Set S) (hBQ : B ⊆ frontier Q)
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥Q))
    (hd : Topology.IsEmbedding d) :
    Disjoint
      ((fun z => (d z).val) ''
        {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}) B := by
  let ds : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S) :=
    ⟨fun z => (d z).val,continuous_subtype_val.comp d.continuous⟩
  have hds : Topology.IsEmbedding ds := Topology.IsEmbedding.subtypeVal.comp hd
  have hopen : IsOpen
      (ds '' {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}) :=
    CurveComplex.LocalSurgery.embedded_surface_disk_interior_isOpen ds hds
  have hsub : ds '' {z | z.val ∈ Metric.ball
      (0 : EuclideanSpace ℝ (Fin 2)) 1} ⊆ Q := by
    rintro y ⟨z,hz,rfl⟩
    exact (d z).property
  have hint : ds '' {z | z.val ∈ Metric.ball
      (0 : EuclideanSpace ℝ (Fin 2)) 1} ⊆ interior Q :=
    interior_maximal hsub hopen
  apply Set.disjoint_left.mpr
  intro y hy hyB
  have hyi : y ∈ interior Q := hint hy
  exact ((mem_interior_iff_notMem_frontier (interior_subset hyi)).mp hyi)
    (hBQ hyB)

#print axioms regional_embedded_subregion_disk_interior_avoids_boundary
