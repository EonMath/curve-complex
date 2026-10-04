import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactVertexNormalization

namespace CurveComplex.Hyperbolic

theorem normalized_circumball_sublevel (c p z : H2)
    (hp : p.re = 0) (hi : p.im = 1) :
    Real.cosh (dist c z) ≤ Real.cosh (dist c p) ↔
      z.re ^ 2 + (z.im - 1) ^ 2 - 2 * c.re * z.re +
        (1 - c.re ^ 2 - c.im ^ 2) * (z.im - 1) ≤ 0 := by
  rw [UpperHalfPlane.cosh_dist', UpperHalfPlane.cosh_dist', hp, hi]
  have hdc : 0 < 2 * c.im * z.im := by positivity
  have hdp : 0 < 2 * c.im * 1 := by positivity
  rw [div_le_div_iff₀ hdc hdp]
  have hci := c.im_pos
  constructor <;> intro h <;> nlinarith [h]

theorem normalized_circumcenter_normSq (c p q : H2)
    (hp : p.re = 0) (hi : p.im = 1) (hq : q.re = 0) (hqp : q ≠ p)
    (hc : Real.cosh (dist c q) = Real.cosh (dist c p)) :
    c.re ^ 2 + c.im ^ 2 = q.im := by
  have hqi : q.im ≠ 1 := by
    intro h
    apply hqp
    apply UpperHalfPlane.ext_re_im
    · exact hq.trans hp.symm
    · exact h.trans hi.symm
  rw [UpperHalfPlane.cosh_dist', UpperHalfPlane.cosh_dist', hp, hi, hq] at hc
  have hdc : 2 * c.im * q.im ≠ 0 := by positivity
  have hdp : 2 * c.im * 1 ≠ 0 := by positivity
  rw [div_eq_div_iff hdc hdp] at hc
  have hf : (q.im - 1) * (c.re ^ 2 + c.im ^ 2 - q.im) = 0 := by
    have hci := c.im_pos
    nlinarith [hc]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_left (sub_ne_zero.mpr hqi))

theorem normalized_circumcenter_side_relation (c p r : H2)
    (hp : p.re = 0) (hi : p.im = 1) (hr : r.re ^ 2 + r.im ^ 2 = 1)
    (hc : Real.cosh (dist c r) = Real.cosh (dist c p)) :
    2 * c.re * r.re = (1 + c.re ^ 2 + c.im ^ 2) * (1 - r.im) := by
  rw [UpperHalfPlane.cosh_dist', UpperHalfPlane.cosh_dist', hp, hi] at hc
  have hdc : 2 * c.im * r.im ≠ 0 := by positivity
  have hdp : 2 * c.im * 1 ≠ 0 := by positivity
  rw [div_eq_div_iff hdc hdp] at hc
  have hci := c.im_pos
  nlinarith [hc, hr]

end CurveComplex.Hyperbolic
