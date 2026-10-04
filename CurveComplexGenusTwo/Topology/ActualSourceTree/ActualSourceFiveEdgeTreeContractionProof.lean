import CurveComplexGenusTwo.Topology.ActualSourceTree.ActualSameChartEighteenPerimeterIntervalsProof
import CurveComplexGenusTwo.Topology.ActualSourceTree.ActualPinnedNorthWholeStripPlacementProof
import CurveComplexGenusTwo.Topology.ActualSourceTree.CollapseLocal
import CurveComplexGenusTwo.Topology.ActualSourceTree.ActualSourcePrimalTreeCollapseTransferProof
open Set Metric Topology
namespace AlternatingSphereCover
/-- The actual five original northern edges are contracted inside the actual
branched cover; the resulting literal quotient is homeomorphic to Total. -/
theorem actual_source_five_edge_tree_contraction :
    let A : Set Total := northDiskFace true ''
      {v : StandardDisk | ∃ p : Sphere, ∃ hp : height p=0,
        (∃ i : Fin 6, i≠0 ∧ closedArcSector i p) ∧ v=diskBoundaryPoint p hp}
    ∃ G : C(Total,Total), Function.Surjective G ∧
      (∀ z w, G z=G w ↔ z=w ∨ (z∈A ∧ w∈A)) ∧
      ∃ h : Quotient (Relation.EqvGen.setoid (fun z w : Total => z∈A ∧ w∈A)) ≃ₜ Total,
        ∀ z, h (Quotient.mk _ z)=G z := by
  dsimp only
  have data := actual_same_chart_eighteen_perimeter_intervals
  dsimp only at data
  obtain ⟨L,H,M0,hL,hH,hML,hMR,Gg,hGg,M3,h3L,h3R,hImages,rest⟩ := data
  obtain ⟨E,hE,hEK,hEint⟩ := actual_pinned_north_five_source_edge_tree_whole_strip H hImages
  obtain ⟨F,hFormula,hFs,hFker,hFboundary⟩ := actual_central_arc_rectangle_collapse
  obtain ⟨G,hPins,hSupport,hSurj,hKer,hHomeo⟩ :=
    actual_source_primal_tree_collapse_transfer E hE hEK hEint F hFs hFker hFboundary
  exact ⟨G,hSurj,hKer,hHomeo⟩
end AlternatingSphereCover
