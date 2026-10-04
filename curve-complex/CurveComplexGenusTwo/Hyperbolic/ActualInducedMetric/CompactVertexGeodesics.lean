import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactVertexNormalization

namespace CurveComplex.Hyperbolic

theorem unit_circleStraightener_re_zero_iff (z : H2) :
    (circleStraightener 0 1 z).re = 0 ↔ z.re ^ 2 + z.im ^ 2 = 1 := by
  constructor
  · intro h
    change (circleStraightener 0 1 z : ℂ).re = 0 at h
    rw [circleStraightener_coe] at h
    simp only [Complex.sub_re, Complex.neg_re, Complex.inv_re,
      Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero,
      Complex.normSq_apply, zero_add, div_one] at h
    have hd : (z.re - 1) ^ 2 + z.im ^ 2 ≠ 0 := by
      nlinarith [z.im_pos, sq_nonneg (z.re - 1)]
    simp only [UpperHalfPlane.re, UpperHalfPlane.im] at *
    simp only [← pow_two] at h
    field_simp [hd] at h
    nlinarith [h]
  · intro h
    apply circleStraightener_re_eq_zero 0 1 (by norm_num) z
    simpa only [sub_zero, one_pow] using h

theorem unit_semicircle_contains_metric_segment (a b z : H2)
    (ha : a.re ^ 2 + a.im ^ 2 = 1)
    (hb : b.re ^ 2 + b.im ^ 2 = 1)
    (hz : dist a z + dist z b = dist a b) :
    z.re ^ 2 + z.im ^ 2 = 1 := by
  have hea := (unit_circleStraightener_re_zero_iff a).mpr ha
  have heb := (unit_circleStraightener_re_zero_iff b).mpr hb
  apply (unit_circleStraightener_re_zero_iff z).mp
  exact ((metric_segment_iff_in_vertical_interval (circleStraightener 0 1)
    a b z hea heb).mp hz).1

theorem actual_right_angle_incident_geodesics (q p r : H2)
    (h : IsRightAngle q p r) (hqp : q ≠ p) :
    ∃ e : H2 ≃ᵢ H2, (e p).re = 0 ∧ (e p).im = 1 ∧
      (∀ z, dist p z + dist z q = dist p q → (e z).re = 0) ∧
      (∀ z, dist p z + dist z r = dist p r →
        (e z).re ^ 2 + (e z).im ^ 2 = 1) := by
  obtain ⟨e, hp, hi, hq, hr⟩ := actual_right_angle_vertex_normalization q p r h hqp
  refine ⟨e, hp, hi, ?_, ?_⟩
  · intro z hz
    exact ((metric_segment_iff_in_vertical_interval e p q z hp hq).mp hz).1
  · intro z hz
    apply unit_semicircle_contains_metric_segment (e p) (e r) (e z)
    · simp only [hp, hi]
      norm_num
    · exact hr
    · simpa only [e.dist_eq] using hz

end CurveComplex.Hyperbolic
