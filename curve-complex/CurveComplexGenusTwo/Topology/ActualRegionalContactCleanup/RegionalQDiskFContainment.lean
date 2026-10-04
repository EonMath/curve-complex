import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalDiskInteriorMeetsRegion
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalEssentialFrontierDiskExclusion
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalQDiskBoundaryAvoidance

open CurveComplex Set Topology

theorem regional_embedded_Q_disk_with_regional_boundary_lies_in_F
    {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (Q F B : Set S) (hBQ : B ⊆ frontier Q) (hFclosed : IsClosed F)
    (J : Type) [Fintype J] (c : J → EssentialCurve S)
    (hfrontier : frontier F = B ∪ ⋃ i, (c i).val.image)
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥Q))
    (hd : Topology.IsEmbedding d)
    (hboundary : (fun z => (d z).val) '' {z | z.val ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} ⊆ F)
    (hboundaryClear : ∀ i, Disjoint (c i).val.image
      ((fun z => (d z).val) '' {z | z.val ∈
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}))
    (hmeet : (Set.range (fun z => (d z).val) ∩ interior F).Nonempty) :
    Set.range (fun z => (d z).val) ⊆ F := by
  let ds : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S) :=
    ⟨fun z => (d z).val,continuous_subtype_val.comp d.continuous⟩
  have hds : Topology.IsEmbedding ds := Topology.IsEmbedding.subtypeVal.comp hd
  have hBavoid := regional_embedded_subregion_disk_interior_avoids_boundary
    Q B hBQ d hd
  have hinside := regional_embedded_disk_interior_meets_open_region
    F ds hds hmeet
  exact regional_essential_frontier_disk_confined F B hFclosed J c hfrontier
    ds hds hboundary hboundaryClear hBavoid hinside

#print axioms regional_embedded_Q_disk_with_regional_boundary_lies_in_F
