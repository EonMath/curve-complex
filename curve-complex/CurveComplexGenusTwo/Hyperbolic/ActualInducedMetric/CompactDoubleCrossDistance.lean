import CurveComplexGenusTwo.Hyperbolic.CompactDoubleTopology
namespace CurveComplex.Hyperbolic
open Set Topology

theorem polygon_double_cross_distance_attained {P : Hexagon} (R : HexagonRegion P)
    (x y : ClosedPolygon R) : ∃ p : PolygonBoundary R,
    dist (Metric.toGlueL (boundaryInclusion_isometry R) (boundaryInclusion_isometry R) x)
      (Metric.toGlueR (boundaryInclusion_isometry R) (boundaryInclusion_isometry R) y) =
    dist x (boundaryInclusion R p) + dist y (boundaryInclusion R p) := by
  let f : PolygonBoundary R → ℝ := fun p =>
    dist x (boundaryInclusion R p) + dist y (boundaryInclusion R p)
  have hf : Continuous f :=
    (continuous_const.dist (boundaryInclusion_isometry R).continuous).add
      (continuous_const.dist (boundaryInclusion_isometry R).continuous)
  obtain ⟨p, _, hp⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hf.continuousOn
  refine ⟨p, ?_⟩
  change (⨅ p, f p) + 0 = f p
  rw [add_zero]
  apply le_antisymm
  · exact ciInf_le ⟨0, Set.forall_mem_range.mpr (fun p => by positivity)⟩ p
  · exact le_ciInf (fun q => hp (Set.mem_univ q))

theorem polygon_double_cross_distance_le_boundary {P : Hexagon} (R : HexagonRegion P)
    (x y : ClosedPolygon R) (p : PolygonBoundary R) :
    dist (Metric.toGlueL (boundaryInclusion_isometry R) (boundaryInclusion_isometry R) x)
      (Metric.toGlueR (boundaryInclusion_isometry R) (boundaryInclusion_isometry R) y) ≤
    dist x (boundaryInclusion R p) + dist y (boundaryInclusion R p) := by
  change (⨅ p : PolygonBoundary R, dist x (boundaryInclusion R p) +
    dist y (boundaryInclusion R p)) + 0 ≤ _
  rw [add_zero]
  exact ciInf_le ⟨0, Set.forall_mem_range.mpr (fun p => by positivity)⟩ p

end CurveComplex.Hyperbolic
