import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.HyperbolicMetricBallConvex
import CurveComplexGenusTwo.Hyperbolic.CompactPolygonGeometry

namespace CurveComplex.Hyperbolic
open Set Topology

theorem cosh_distance_no_local_maximum (c z : H2) (U : Set H2)
    (hU : IsOpen U) (hz : z ∈ U)
    (hmax : ∀ w ∈ U, Real.cosh (dist c w) ≤ Real.cosh (dist c z)) : False := by
  let f : ℝ → H2 := fun t => t +ᵥ z
  have hf : Continuous f := by
    apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
    change Continuous (fun t : ℝ => (t : ℂ) + (z : ℂ))
    exact Complex.continuous_ofReal.add continuous_const
  have hopen : IsOpen (f ⁻¹' U) := hU.preimage hf
  have hz0 : (0 : ℝ) ∈ f ⁻¹' U := by simpa [f] using hz
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen 0 hz0
  have ht : 0 < δ / 2 := by linarith
  have hp : f (δ / 2) ∈ U := hball (by
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero]
    rw [abs_of_pos ht]
    linarith)
  have hn : f (-(δ / 2)) ∈ U := hball (by
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_neg]
    rw [abs_of_pos ht]
    linarith)
  have hplus := hmax _ hp
  have hminus := hmax _ hn
  rw [UpperHalfPlane.cosh_dist', UpperHalfPlane.cosh_dist'] at hplus hminus
  simp only [f, UpperHalfPlane.vadd_re, UpperHalfPlane.vadd_im] at hplus hminus
  have hd : 0 < 2 * c.im * z.im := by positivity
  rw [div_le_div_iff_of_pos_right hd] at hplus hminus
  nlinarith [sq_pos_of_pos ht]

theorem HexagonRegion.cosh_distance_boundary_maximum {P : Hexagon}
    (R : HexagonRegion P) (c : H2) (B : ℝ)
    (hboundary : ∀ z ∈ frontier R.interior, Real.cosh (dist c z) ≤ B) :
    ∀ z ∈ closure R.interior, Real.cosh (dist c z) ≤ B := by
  have hf : Continuous (fun z : H2 => Real.cosh (dist c z)) :=
    Real.continuous_cosh.comp (continuous_const.dist continuous_id)
  obtain ⟨m, hm, hmax⟩ := (closedPolygon_isCompact R).exists_isMaxOn
    (R.nonempty_interior.mono subset_closure) hf.continuousOn
  have hmnot : m ∉ R.interior := by
    intro hmi
    exact cosh_distance_no_local_maximum c m R.interior R.open_interior hmi
      (fun z hz => hmax (subset_closure hz))
  have hmfront : m ∈ frontier R.interior := by
    rw [frontier, R.open_interior.interior_eq]
    exact ⟨hm, hmnot⟩
  intro z hz
  exact (hmax hz).trans (hboundary m hmfront)

theorem HexagonRegion.cosh_distance_vertex_bound {P : Hexagon}
    (R : HexagonRegion P) (c : H2) (B : ℝ)
    (hvertices : ∀ i, Real.cosh (dist c (P.vertex i)) ≤ B) :
    ∀ z ∈ closure R.interior, Real.cosh (dist c z) ≤ B := by
  apply R.cosh_distance_boundary_maximum c B
  intro z hz
  rw [R.boundary_is_edges] at hz
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
  exact (metric_segment_cosh_distance_le_max c (P.vertex i) (P.vertex (i + 1)) z hi).trans
    (max_le (hvertices i) (hvertices (i + 1)))

end CurveComplex.Hyperbolic
