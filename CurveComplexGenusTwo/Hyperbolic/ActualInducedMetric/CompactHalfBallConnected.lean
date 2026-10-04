import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactSeamDevelopment
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Complex.Convex
namespace CurveComplex.Hyperbolic
open Set Topology

private theorem complex_ball_halfplanes_preconnected (c : ℂ) (r : ℝ) :
    IsPreconnected (Metric.ball c r ∩ {z : ℂ | 0 < z.re}) ∧
    IsPreconnected (Metric.ball c r ∩ {z : ℂ | z.re < 0}) := by
  constructor
  · exact ((convex_ball c r).inter
      (convex_halfSpace_re_gt 0)).isPreconnected
  · exact ((convex_ball c r).inter
      (convex_halfSpace_re_lt 0)).isPreconnected

theorem hyperbolic_half_ball_isPreconnected (x : H2) (r : ℝ) :
    IsPreconnected (Metric.ball x r ∩ {z : H2 | 0 < z.re}) ∧
    IsPreconnected (Metric.ball x r ∩ {z : H2 | z.re < 0}) := by
  have hepos : ((↑) : H2 → ℂ) '' (Metric.ball x r ∩ {z : H2 | 0 < z.re}) =
      Metric.ball (x.center r : ℂ) (x.im * Real.sinh r) ∩ {z : ℂ | 0 < z.re} := by
    change ((↑) : H2 → ℂ) '' (Metric.ball x r ∩
      ((↑) : H2 → ℂ) ⁻¹' {w : ℂ | 0 < w.re}) = _
    rw [Set.image_inter_preimage, UpperHalfPlane.image_coe_ball]
  have heneg : ((↑) : H2 → ℂ) '' (Metric.ball x r ∩ {z : H2 | z.re < 0}) =
      Metric.ball (x.center r : ℂ) (x.im * Real.sinh r) ∩ {z : ℂ | z.re < 0} := by
    change ((↑) : H2 → ℂ) '' (Metric.ball x r ∩
      ((↑) : H2 → ℂ) ⁻¹' {w : ℂ | w.re < 0}) = _
    rw [Set.image_inter_preimage, UpperHalfPlane.image_coe_ball]
  have h := complex_ball_halfplanes_preconnected (x.center r : ℂ) (x.im * Real.sinh r)
  constructor
  · apply (UpperHalfPlane.isEmbedding_coe.isInducing.isPreconnected_image).mp
    rw [hepos]
    exact h.1
  · apply (UpperHalfPlane.isEmbedding_coe.isInducing.isPreconnected_image).mp
    rw [heneg]
    exact h.2

end CurveComplex.Hyperbolic
