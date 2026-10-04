import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactGeodesicHalfPlanes
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactVertexReflections

namespace CurveComplex.Hyperbolic

theorem metric_segment_crosses_unit_semicircle (a b : H2)
    (ha : a.re ^ 2 + a.im ^ 2 ≤ 1) (hb : 1 ≤ b.re ^ 2 + b.im ^ 2) :
    ∃ p : H2, p.re ^ 2 + p.im ^ 2 = 1 ∧ dist a p + dist p b = dist a b := by
  by_cases hab : a = b
  · refine ⟨a, le_antisymm ha (hab ▸ hb), ?_⟩
    simp
  · obtain ⟨f, hf, _, h0, h1, him⟩ := metric_segment_has_parametrization a b hab
    have hfc : Continuous (fun t : ℝ => (f t).re ^ 2 + (f t).im ^ 2) :=
      ((UpperHalfPlane.continuous_re.comp hf).pow 2).add
        ((UpperHalfPlane.continuous_im.comp hf).pow 2)
    have h01 : (0 : ℝ) ≤ 1 := by norm_num
    have hone : (1 : ℝ) ∈ Set.Icc ((f 0).re ^ 2 + (f 0).im ^ 2)
        ((f 1).re ^ 2 + (f 1).im ^ 2) := by
      rw [h0, h1]
      exact ⟨ha, hb⟩
    obtain ⟨t, ht, hft⟩ := intermediate_value_Icc h01 hfc.continuousOn hone
    refine ⟨f t, hft, ?_⟩
    have hmem : f t ∈ {z : H2 | dist a z + dist z b = dist a b} := by
      rw [← him]
      exact ⟨t, ht, rfl⟩
    exact hmem

theorem reflected_unit_circle_crossing_in_inner_quarter_ball (c a b : H2) {r : ℝ}
    (hc : c.re ^ 2 + c.im ^ 2 = 1) (ha : 0 ≤ a.re) (hb : 0 ≤ b.re)
    (haN : a.re ^ 2 + a.im ^ 2 ≤ 1) (hbN : b.re ^ 2 + b.im ^ 2 ≤ 1)
    (haBall : a ∈ Metric.ball c r) (hbBall : b ∈ Metric.ball c r) :
    ∃ p ∈ Metric.ball c r, 0 ≤ p.re ∧ p.re ^ 2 + p.im ^ 2 = 1 ∧
      dist a p + dist b p = dist a (unitCircleReflectionEquiv b) := by
  have hbOutside : 1 ≤ (unitCircleReflectionEquiv b).re ^ 2 +
      (unitCircleReflectionEquiv b).im ^ 2 := by
    rw [unitCircleReflection_normSq]
    have hd : 0 < b.re ^ 2 + b.im ^ 2 := by nlinarith [b.im_pos]
    rw [le_div_iff₀ hd]
    simpa using hbN
  obtain ⟨p, hp, hseg⟩ := metric_segment_crosses_unit_semicircle a
    (unitCircleReflectionEquiv b) haN hbOutside
  have hbRe : 0 ≤ (unitCircleReflectionEquiv b).re := by
    rw [unitCircleReflection_re]
    exact div_nonneg hb (by positivity)
  have hpRe := metric_segment_in_positive_vertical_halfplane a
    (unitCircleReflectionEquiv b) p ha hbRe hseg
  have hcfix := (unitCircleReflection_fixed_iff c).mpr hc
  have hpfix := (unitCircleReflection_fixed_iff p).mpr hp
  have hbBall' : unitCircleReflectionEquiv b ∈ Metric.ball c r := by
    have hd : dist (unitCircleReflectionEquiv b) c = dist b c := by
      calc
        _ = dist (unitCircleReflectionEquiv b) (unitCircleReflectionEquiv c) :=
          congrArg (dist (unitCircleReflectionEquiv b)) hcfix.symm
        _ = dist b c := unitCircleReflectionEquiv.dist_eq _ _
    simpa only [Metric.mem_ball, hd] using hbBall
  have hpBall := metric_segment_stays_in_hyperbolic_ball c a
    (unitCircleReflectionEquiv b) p haBall hbBall' hseg
  refine ⟨p, hpBall, hpRe, hp, ?_⟩
  have hd : dist p (unitCircleReflectionEquiv b) = dist b p := by
    calc
      _ = dist (unitCircleReflectionEquiv p) (unitCircleReflectionEquiv b) :=
        congrArg (fun v => dist v (unitCircleReflectionEquiv b)) hpfix.symm
      _ = dist p b := unitCircleReflectionEquiv.dist_eq _ _
      _ = dist b p := dist_comm _ _
  rwa [hd] at hseg

theorem reflected_vertical_crossing_in_inner_quarter_ball (c a b : H2) {r : ℝ}
    (hc : c.re = 0) (ha : 0 ≤ a.re) (hb : 0 ≤ b.re)
    (haN : a.re ^ 2 + a.im ^ 2 ≤ 1) (hbN : b.re ^ 2 + b.im ^ 2 ≤ 1)
    (haBall : a ∈ Metric.ball c r) (hbBall : b ∈ Metric.ball c r) :
    ∃ p ∈ Metric.ball c r, p.re = 0 ∧ p.re ^ 2 + p.im ^ 2 ≤ 1 ∧
      dist a p + dist b p = dist a (verticalReflectionEquiv b) := by
  obtain ⟨p, hpBall, hp, hdist⟩ := reflected_geodesic_crossing_in_ball c a b hc ha hb haBall hbBall
  have hpfix := (verticalReflection_fixed_iff p).mpr hp
  have hd : dist p (verticalReflectionEquiv b) = dist b p := by
    calc
      _ = dist (verticalReflectionEquiv p) (verticalReflectionEquiv b) :=
        congrArg (fun v => dist v (verticalReflectionEquiv b)) hpfix.symm
      _ = dist p b := verticalReflectionEquiv.dist_eq _ _
      _ = dist b p := dist_comm _ _
  have hseg : dist a p + dist p (verticalReflectionEquiv b) =
      dist a (verticalReflectionEquiv b) := by rwa [hd]
  have hbN' : (verticalReflectionEquiv b).re ^ 2 + (verticalReflectionEquiv b).im ^ 2 ≤ 1 := by
    simpa only [verticalReflection_re, verticalReflection_im, neg_sq] using hbN
  exact ⟨p, hpBall, hp, metric_segment_in_unit_semicircle_inside a
    (verticalReflectionEquiv b) p haN hbN' hseg, hdist⟩

end CurveComplex.Hyperbolic
