import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactEdgeReflection
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.HyperbolicMetricBallConvex
namespace CurveComplex.Hyperbolic
open Set Topology

noncomputable def verticalReflectionEquiv : H2 ≃ᵢ H2 :=
  let T := realTranslationIsometry IdealHexagonDouble.sideZeroAbscissa
  T.trans (IdealHexagonDouble.sideZeroReflectionEquiv.trans T.symm)

@[simp]
theorem verticalReflection_re (z : H2) : (verticalReflectionEquiv z).re = -z.re := by
  change (-IdealHexagonDouble.sideZeroAbscissa +ᵥ
    IdealHexagonDouble.sideZeroReflection (IdealHexagonDouble.sideZeroAbscissa +ᵥ z)).re = -z.re
  simp only [UpperHalfPlane.vadd_re, IdealHexagonDouble.sideZeroReflection_re]
  ring

@[simp]
theorem verticalReflection_im (z : H2) : (verticalReflectionEquiv z).im = z.im := by
  change (-IdealHexagonDouble.sideZeroAbscissa +ᵥ
    IdealHexagonDouble.sideZeroReflection (IdealHexagonDouble.sideZeroAbscissa +ᵥ z)).im = z.im
  simp only [UpperHalfPlane.vadd_im, IdealHexagonDouble.sideZeroReflection_im]

theorem verticalReflection_fixed_iff (z : H2) : verticalReflectionEquiv z = z ↔ z.re = 0 := by
  constructor
  · intro h
    have := congrArg UpperHalfPlane.re h
    simp only [verticalReflection_re] at this
    linarith
  · intro h
    apply UpperHalfPlane.ext_re_im
    · simp [h]
    · exact verticalReflection_im z

theorem verticalReflection_involutive : Function.Involutive verticalReflectionEquiv := by
  intro z
  apply UpperHalfPlane.ext_re_im <;> simp

theorem metric_segment_crosses_vertical (a b : H2) (ha : 0 ≤ a.re) (hb : b.re ≤ 0) :
    ∃ p : H2, p.re = 0 ∧ dist a p + dist p b = dist a b := by
  by_cases hab : a = b
  · refine ⟨a, le_antisymm (hab ▸ hb) ha, ?_⟩
    simp
  · obtain ⟨f, hf, _, h0, h1, him⟩ := metric_segment_has_parametrization a b hab
    have hfc : Continuous (fun t : ℝ => (f t).re) := UpperHalfPlane.continuous_re.comp hf
    have h01 : (0 : ℝ) ≤ 1 := by norm_num
    have hzero : (0 : ℝ) ∈ Set.Icc ((f 1).re) ((f 0).re) := by
      rw [h0, h1]
      exact ⟨hb, ha⟩
    obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' h01 hfc.continuousOn hzero
    refine ⟨f t, hft, ?_⟩
    have hmem : f t ∈ {z : H2 | dist a z + dist z b = dist a b} := by
      rw [← him]
      exact ⟨t, ht, rfl⟩
    exact hmem

theorem reflected_geodesic_crossing_in_ball (c a b : H2) {r : ℝ}
    (hc : c.re = 0) (ha : 0 ≤ a.re) (hb : 0 ≤ b.re)
    (haBall : a ∈ Metric.ball c r) (hbBall : b ∈ Metric.ball c r) :
    ∃ p ∈ Metric.ball c r, p.re = 0 ∧
      dist a p + dist b p = dist a (verticalReflectionEquiv b) := by
  obtain ⟨p, hp, hseg⟩ := metric_segment_crosses_vertical a (verticalReflectionEquiv b) ha
    (by simp; linarith)
  have hcfix := (verticalReflection_fixed_iff c).mpr hc
  have hpfix := (verticalReflection_fixed_iff p).mpr hp
  have hbBall' : verticalReflectionEquiv b ∈ Metric.ball c r := by
    have hd : dist (verticalReflectionEquiv b) c = dist b c := by
      calc
        _ = dist (verticalReflectionEquiv b) (verticalReflectionEquiv c) :=
          congrArg (dist (verticalReflectionEquiv b)) hcfix.symm
        _ = dist b c := verticalReflectionEquiv.dist_eq _ _
    simpa only [Metric.mem_ball, hd] using hbBall
  have hpBall := metric_segment_stays_in_hyperbolic_ball c a (verticalReflectionEquiv b) p
    haBall hbBall' hseg
  refine ⟨p, hpBall, hp, ?_⟩
  have hd : dist p (verticalReflectionEquiv b) = dist b p := by
    calc
      _ = dist (verticalReflectionEquiv p) (verticalReflectionEquiv b) :=
        congrArg (fun v => dist v (verticalReflectionEquiv b)) hpfix.symm
      _ = dist p b := verticalReflectionEquiv.dist_eq _ _
      _ = dist b p := dist_comm _ _
  rwa [hd] at hseg
end CurveComplex.Hyperbolic
