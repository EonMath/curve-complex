import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactHalfBallConnected
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactVertexReflections

namespace CurveComplex.Hyperbolic
open Set Topology

theorem hyperbolic_inner_quarter_ball_isPreconnected (x : H2) (r : ℝ) :
    IsPreconnected (Metric.ball x r ∩
      {z : H2 | 0 < z.re ∧ z.re ^ 2 + z.im ^ 2 < 1}) ∧
    IsPreconnected (Metric.ball x r ∩
      {z : H2 | z.re < 0 ∧ z.re ^ 2 + z.im ^ 2 < 1}) := by
  have he : ∀ (s : Set ℂ),
      ((↑) : H2 → ℂ) '' (Metric.ball x r ∩ ((↑) : H2 → ℂ) ⁻¹' s) =
      Metric.ball (x.center r : ℂ) (x.im * Real.sinh r) ∩ s := by
    intro s
    rw [Set.image_inter_preimage, UpperHalfPlane.image_coe_ball]
  have hb : {z : ℂ | z.re ^ 2 + z.im ^ 2 < 1} = Metric.ball 0 1 := by
    ext z
    simp only [Set.mem_setOf_eq, Metric.mem_ball, dist_zero_right]
    have hn := Complex.normSq_eq_norm_sq z
    simp only [Complex.normSq_apply] at hn
    constructor <;> intro h <;> nlinarith [norm_nonneg z]
  constructor
  · apply UpperHalfPlane.isEmbedding_coe.isInducing.isPreconnected_image.mp
    change IsPreconnected (((↑) : H2 → ℂ) ''
      (Metric.ball x r ∩ ((↑) : H2 → ℂ) ⁻¹'
        ({z : ℂ | 0 < z.re} ∩ {z : ℂ | z.re ^ 2 + z.im ^ 2 < 1})))
    rw [he, hb]
    exact ((convex_ball _ _).inter
      ((convex_halfSpace_re_gt 0).inter (convex_ball 0 1))).isPreconnected
  · apply UpperHalfPlane.isEmbedding_coe.isInducing.isPreconnected_image.mp
    change IsPreconnected (((↑) : H2 → ℂ) ''
      (Metric.ball x r ∩ ((↑) : H2 → ℂ) ⁻¹'
        ({z : ℂ | z.re < 0} ∩ {z : ℂ | z.re ^ 2 + z.im ^ 2 < 1})))
    rw [he, hb]
    exact ((convex_ball _ _).inter
      ((convex_halfSpace_re_lt 0).inter (convex_ball 0 1))).isPreconnected

theorem hyperbolic_outer_quarter_ball_isPreconnected (x : H2) (r : ℝ)
    (hx : x.re ^ 2 + x.im ^ 2 = 1) :
    IsPreconnected (Metric.ball x r ∩
      {z : H2 | 0 < z.re ∧ 1 < z.re ^ 2 + z.im ^ 2}) ∧
    IsPreconnected (Metric.ball x r ∩
      {z : H2 | z.re < 0 ∧ 1 < z.re ^ 2 + z.im ^ 2}) := by
  have hfix := (unitCircleReflection_fixed_iff x).mpr hx
  have hball : ∀ z : H2, unitCircleReflectionEquiv z ∈ Metric.ball x r ↔
      z ∈ Metric.ball x r := by
    intro z
    simp only [Metric.mem_ball]
    have hd : dist (unitCircleReflectionEquiv z) x = dist z x := by
      calc
        _ = dist (unitCircleReflectionEquiv z) (unitCircleReflectionEquiv x) :=
          congrArg (dist (unitCircleReflectionEquiv z)) hfix.symm
        _ = dist z x := unitCircleReflectionEquiv.dist_eq _ _
    rw [hd]
  have hpos : ∀ z : H2, 0 < (unitCircleReflectionEquiv z).re ↔ 0 < z.re := by
    intro z
    rw [unitCircleReflection_re]
    exact div_pos_iff_of_pos_right (by nlinarith [z.im_pos])
  have hneg : ∀ z : H2, (unitCircleReflectionEquiv z).re < 0 ↔ z.re < 0 := by
    intro z
    rw [unitCircleReflection_re]
    have hd : 0 < z.re ^ 2 + z.im ^ 2 := by nlinarith [z.im_pos]
    rw [div_lt_iff₀ hd]
    simp only [zero_mul]
  have himage : ∀ (s : Set H2), unitCircleReflectionEquiv '' s =
      unitCircleReflectionEquiv ⁻¹' s := by
    intro s
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      change unitCircleReflectionEquiv (unitCircleReflectionEquiv w) ∈ s
      rw [unitCircleReflection_involutive w]
      exact hw
    · intro hz
      exact ⟨unitCircleReflectionEquiv z, hz, unitCircleReflection_involutive z⟩
  have hp := (hyperbolic_inner_quarter_ball_isPreconnected x r).1.image
    unitCircleReflectionEquiv unitCircleReflectionEquiv.continuous.continuousOn
  have hn := (hyperbolic_inner_quarter_ball_isPreconnected x r).2.image
    unitCircleReflectionEquiv unitCircleReflectionEquiv.continuous.continuousOn
  rw [himage] at hp hn
  constructor
  · convert hp using 1
    ext z
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage,
      hball, hpos, unitCircleReflection_inner_iff_outer]
  · convert hn using 1
    ext z
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage,
      hball, hneg, unitCircleReflection_inner_iff_outer]

end CurveComplex.Hyperbolic
