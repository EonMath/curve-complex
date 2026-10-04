import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.DevelopmentChainLawsCandidate

namespace CurveComplex.Hyperbolic
open Set Topology
variable {E : Type} [TopologicalSpace E]

theorem development_chain_ball_contains_open_chart_neighborhood (F : Set (OpenPartialHomeomorph E H2))
    (e : OpenPartialHomeomorph E H2) (he : e ∈ F)
    (x : E) (hx : x ∈ e.source) (R : ℝ) (hR : 0 < R) :
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
      U ⊆ {y | developmentChainEDist F x y < ENNReal.ofReal R} := by
  let U := e.source ∩ e ⁻¹' Metric.ball (e x) R
  have hU : IsOpen U := e.isOpen_inter_preimage Metric.isOpen_ball
  refine ⟨U, hU, ⟨hx, Metric.mem_ball_self hR⟩, ?_⟩
  intro y hy
  have hle := developmentChainEDist_le_chain
    (DevelopmentChain.cons e he hx hy.1 (DevelopmentChain.nil y))
  simp only [add_zero, edist_dist] at hle
  apply lt_of_le_of_lt hle
  apply (ENNReal.ofReal_lt_ofReal_iff hR).mpr
  simpa only [Set.mem_preimage, Metric.mem_ball, dist_comm] using hy.2

end CurveComplex.Hyperbolic
