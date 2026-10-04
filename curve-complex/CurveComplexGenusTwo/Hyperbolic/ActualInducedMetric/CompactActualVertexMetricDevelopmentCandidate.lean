import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactActualCenteredVertexConeChart

namespace CurveComplex.Hyperbolic
open Set Topology

theorem regularHexagon_actual_vertex_centered_metric_development (i : Fin 6) :
    ∃ c : ClosedPolygon regularHexagonRegion,
      (c : H2) = regularHexagonCandidate.vertex i ∧
      ∃ e : OpenPartialHomeomorph
        (Metric.GlueSpace (boundaryInclusion_isometry regularHexagonRegion)
          (boundaryInclusion_isometry regularHexagonRegion)) HalfTurnMetricCone,
        Metric.toGlueL (boundaryInclusion_isometry regularHexagonRegion)
          (boundaryInclusion_isometry regularHexagonRegion) c ∈ e.source ∧
        ∃ p : H2, p.re = 0 ∧ p.im = 1 ∧ ∃ r : ℝ, 0 < r ∧
          e.target = Metric.ball (toHalfTurnMetricCone p) r ∧
          e (Metric.toGlueL (boundaryInclusion_isometry regularHexagonRegion)
            (boundaryInclusion_isometry regularHexagonRegion) c) = toHalfTurnMetricCone p ∧
          (∀ y ∈ e.source, ∀ z ∈ e.source, dist (e y) (e z) = dist y z) := by
  classical
  obtain ⟨c, hc, r, hr, f, hf, p, hp, hi, hy, hcenterf⟩ := regularHexagon_actual_vertex_centered_cone_ball i
  let U := Metric.ball
    (Metric.toGlueL (boundaryInclusion_isometry regularHexagonRegion)
      (boundaryInclusion_isometry regularHexagonRegion) c) r
  have hcenter : Metric.toGlueL (boundaryInclusion_isometry regularHexagonRegion)
      (boundaryInclusion_isometry regularHexagonRegion) c ∈ U := Metric.mem_ball_self hr
  let : Nonempty U := ⟨⟨_, hcenter⟩⟩
  have hopen : IsOpenEmbedding f := ⟨hf.isEmbedding, by rw [hy]; exact Metric.isOpen_ball⟩
  let s : TopologicalSpace.Opens
      (Metric.GlueSpace (boundaryInclusion_isometry regularHexagonRegion)
        (boundaryInclusion_isometry regularHexagonRegion)) := ⟨U, Metric.isOpen_ball⟩
  let a := s.openPartialHomeomorphSubtypeCoe (inferInstance : Nonempty U)
  let b := hopen.toOpenPartialHomeomorph f
  refine ⟨c, hc, a.symm.trans b, ?_, p, hp, hi, r, hr, ?_, ?_, ?_⟩
  · simpa [a, b, s, U] using hcenter
  · simp [a, b, s, hy]
  · change f (a.symm _) = _
    have hv : (a.symm (Metric.toGlueL (boundaryInclusion_isometry regularHexagonRegion)
        (boundaryInclusion_isometry regularHexagonRegion) c)).val =
        Metric.toGlueL (boundaryInclusion_isometry regularHexagonRegion)
          (boundaryInclusion_isometry regularHexagonRegion) c := by
      apply a.right_inv
      simpa [a, s] using hcenter
    have heq : a.symm (Metric.toGlueL (boundaryInclusion_isometry regularHexagonRegion)
        (boundaryInclusion_isometry regularHexagonRegion) c) = ⟨_, Metric.mem_ball_self hr⟩ :=
      Subtype.ext hv
    rw [heq]
    exact hcenterf

  · intro y hy z hz
    change dist (f (a.symm y)) (f (a.symm z)) = dist y z
    rw [hf.dist_eq]
    change dist (a.symm y).val (a.symm z).val = dist y z
    have hyt : y ∈ a.target := hy.1
    have hzt : z ∈ a.target := hz.1
    have hyy : (a.symm y).val = y := a.right_inv hyt
    have hzz : (a.symm z).val = z := a.right_inv hzt
    rw [hyy, hzz]

end CurveComplex.Hyperbolic
