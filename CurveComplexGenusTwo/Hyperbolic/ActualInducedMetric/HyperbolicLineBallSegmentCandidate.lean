import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactSupportingGeodesicCandidate

namespace CurveComplex.Hyperbolic
open Set

set_option maxHeartbeats 1000000 in
theorem vertical_geodesic_equal_radius_ball_segment (c a b z : H2)
    (hab : a ≠ b) (ha : a.re = 0) (hb : b.re = 0) (hz : z.re = 0)
    (heq : Real.cosh (dist c a) = Real.cosh (dist c b))
    (hle : Real.cosh (dist c z) ≤ Real.cosh (dist c a)) :
    dist a z + dist z b = dist a b := by
  let K := c.re ^ 2 + c.im ^ 2
  have hid (v : H2) (hv : v.re = 0) :
      2 * c.im * v.im * Real.cosh (dist c v) = K + v.im ^ 2 := by
    rw [UpperHalfPlane.cosh_dist', hv]
    dsimp [K]
    field_simp
    ring
  have hA := hid a ha
  have hB := hid b hb
  have hZ := hid z hz
  have hne : a.im ≠ b.im := by
    intro h; exact hab (UpperHalfPlane.ext_re_im (ha.trans hb.symm) h)
  rw [← heq] at hB
  have hAB : K = a.im * b.im := by
    have h₁ := congrArg (fun x : ℝ => x * b.im) hA
    have h₂ := congrArg (fun x : ℝ => x * a.im) hB
    have hfactor : (a.im - b.im) * (a.im * b.im - K) = 0 := by nlinarith [h₁, h₂]
    have h := (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hne)
    linarith
  have hi : (K + z.im ^ 2) * a.im ≤ (K + a.im ^ 2) * z.im := by
    have h := mul_le_mul_of_nonneg_left hle
      (show 0 ≤ 2 * c.im * a.im * z.im by positivity)
    have h₁ := congrArg (fun x : ℝ => x * z.im) hA
    have h₂ := congrArg (fun x : ℝ => x * a.im) hZ
    nlinarith [h₁, h₂]
  rw [hAB] at hi
  have hprod : (z.im - a.im) * (z.im - b.im) ≤ 0 := by
    apply (mul_le_mul_iff_right₀ a.im_pos).mp
    nlinarith [hi]
  have hlogs : Real.log z.im ∈ uIcc (Real.log a.im) (Real.log b.im) := by
    rcases mul_nonpos_iff.mp hprod with h | h
    · have haz : a.im ≤ z.im := by linarith [h.1]
      have hzb : z.im ≤ b.im := by linarith [h.2]
      rw [uIcc_of_le (Real.log_le_log a.im_pos (haz.trans hzb))]
      exact ⟨Real.log_le_log a.im_pos haz, Real.log_le_log z.im_pos hzb⟩
    · have hbz : b.im ≤ z.im := by linarith [h.2]
      have hza : z.im ≤ a.im := by linarith [h.1]
      rw [uIcc_of_ge (Real.log_le_log b.im_pos (hbz.trans hza))]
      exact ⟨Real.log_le_log b.im_pos hbz, Real.log_le_log z.im_pos hza⟩
  exact (metric_segment_iff_in_vertical_interval (IsometryEquiv.refl H2) a b z ha hb).mpr ⟨hz, hlogs⟩

end CurveComplex.Hyperbolic
