import CurveComplexGenusTwo.Hyperbolic.CompactHexagonRegion

namespace CurveComplex.Hyperbolic
open Set Topology

noncomputable instance polygonBoundary_compactSpace {P : Hexagon}
    (R : HexagonRegion P) : CompactSpace (PolygonBoundary R) := by
  have hclosed : IsClosed {z : ClosedPolygon R | (z : H2) ∈ frontier R.interior} :=
    isClosed_frontier.preimage continuous_subtype_val
  exact isCompact_iff_compactSpace.mp hclosed.isCompact

theorem polygon_double_cross_copy_eq_iff {P : Hexagon} (R : HexagonRegion P)
    (x y : ClosedPolygon R) :
    Metric.toGlueL (boundaryInclusion_isometry R) (boundaryInclusion_isometry R) x =
      Metric.toGlueR (boundaryInclusion_isometry R) (boundaryInclusion_isometry R) y ↔
      x = y ∧ (x : H2) ∈ frontier R.interior := by
  constructor
  · intro hxy
    have hd : dist
        (Metric.toGlueL (boundaryInclusion_isometry R) (boundaryInclusion_isometry R) x)
        (Metric.toGlueR (boundaryInclusion_isometry R) (boundaryInclusion_isometry R) y) = 0 := by
      rw [hxy, dist_self]
    let f : PolygonBoundary R → ℝ := fun p =>
      dist x (boundaryInclusion R p) + dist y (boundaryInclusion R p)
    have hf : Continuous f :=
      (continuous_const.dist (boundaryInclusion_isometry R).continuous).add
        (continuous_const.dist (boundaryInclusion_isometry R).continuous)
    obtain ⟨p, _, hp⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty) hf.continuousOn
    have hinf : (⨅ p, f p) = f p := by
      apply le_antisymm
      · exact ciInf_le ⟨0, Set.forall_mem_range.mpr (fun p => by positivity)⟩ p
      · exact le_ciInf (fun q => hp (Set.mem_univ q))
    change (⨅ p, f p) + 0 = 0 at hd
    rw [hinf, add_zero] at hd
    have hxp : x = boundaryInclusion R p := by
      apply eq_of_dist_eq_zero
      dsimp [f] at hd
      linarith [dist_nonneg (x := x) (y := boundaryInclusion R p),
        dist_nonneg (x := y) (y := boundaryInclusion R p)]
    have hyp : y = boundaryInclusion R p := by
      apply eq_of_dist_eq_zero
      dsimp [f] at hd
      linarith [dist_nonneg (x := x) (y := boundaryInclusion R p),
        dist_nonneg (x := y) (y := boundaryInclusion R p)]
    refine ⟨hxp.trans hyp.symm, ?_⟩
    rw [hxp]
    exact p.property
  · rintro ⟨rfl, hx⟩
    exact congrFun (Metric.toGlue_commute
      (boundaryInclusion_isometry R) (boundaryInclusion_isometry R)) ⟨x, hx⟩

end CurveComplex.Hyperbolic
