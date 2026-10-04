import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactDiscGeodesicPolynomialCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactVertexGeodesics

namespace CurveComplex.Hyperbolic

theorem supporting_semicircle_vertical_isometry (c r : ℝ) (hr : 0 < r) :
    ∃ e : H2 ≃ᵢ H2, ∀ z : H2,
      (z.re - c) ^ 2 + z.im ^ 2 = r ^ 2 ↔ (e z).re = 0 := by
  let f := (realTranslationIsometry (-c)).trans
    (positiveDilationIsometry ⟨r⁻¹, inv_pos.mpr hr⟩)
  refine ⟨f.trans (circleStraightener 0 1), ?_⟩
  intro z
  change (z.re - c) ^ 2 + z.im ^ 2 = r ^ 2 ↔ (circleStraightener 0 1 (f z)).re = 0
  rw [unit_circleStraightener_re_zero_iff]
  have hfr : (f z).re = (z.re - c) / r := by
    change ((⟨r⁻¹, inv_pos.mpr hr⟩ : {x : ℝ // 0 < x}) • ((-c) +ᵥ z)).re = _
    rw [UpperHalfPlane.pos_real_re, UpperHalfPlane.vadd_re]
    ring
  have hfi : (f z).im = z.im / r := by
    change ((⟨r⁻¹, inv_pos.mpr hr⟩ : {x : ℝ // 0 < x}) • ((-c) +ᵥ z)).im = _
    rw [UpperHalfPlane.pos_real_im, UpperHalfPlane.vadd_im]
    ring
  rw [hfr, hfi]
  field_simp

set_option maxHeartbeats 1000000 in
theorem compact_disc_side_supporting_geodesic (c : ℂ) (hc : Complex.normSq c = 2) :
    ∃ e : H2 ≃ᵢ H2, ∀ z : H2,
      Complex.normSq (cayley z : ℂ) - 2 * (star c * (cayley z : ℂ)).re + 1 = 0 ↔
      (e z).re = 0 := by
  have hn : c.re ^ 2 + c.im ^ 2 = 2 := by simpa only [Complex.normSq_apply, ← pow_two] using hc
  have hpoly (z : H2) :
      Complex.normSq (cayley z : ℂ) - 2 * (star c * (cayley z : ℂ)).re + 1 = 0 ↔
      (1 - c.re) * (z.re ^ 2 + z.im ^ 2) + (1 + c.re) + 2 * c.im * z.re = 0 := by
    have h := cayley_disc_circle_signed_polynomial c z
    have hd : z.re ^ 2 + (z.im + 1) ^ 2 ≠ 0 := by nlinarith [z.im_pos, sq_nonneg z.re]
    constructor
    · intro hz; rw [hz, zero_mul] at h; linarith
    · intro hz; rw [hz, mul_zero] at h
      exact (mul_eq_zero.mp h).resolve_right hd
  by_cases hu : c.re = 1
  · have hv : c.im ≠ 0 := by intro hv; rw [hu, hv] at hn; norm_num at hn
    refine ⟨realTranslationIsometry (c.im⁻¹), ?_⟩
    intro z
    rw [hpoly]
    change _ ↔ (c.im⁻¹ +ᵥ z).re = 0
    rw [UpperHalfPlane.vadd_re, hu]
    simp only [sub_self, zero_mul, zero_add]
    constructor <;> intro h
    · have h' : c.im * (c.im⁻¹ + z.re) = 0 := by rw [mul_add, mul_inv_cancel₀ hv]; linarith
      exact (mul_eq_zero.mp h').resolve_left hv
    · have h' := congrArg (fun r : ℝ => c.im * r) h
      rw [mul_add, mul_inv_cancel₀ hv, mul_zero] at h'
      linarith
  · have hd : c.re - 1 ≠ 0 := sub_ne_zero.mpr hu
    let k := c.im / (c.re - 1)
    let r := 1 / |c.re - 1|
    have hr : 0 < r := one_div_pos.mpr (abs_pos.mpr hd)
    obtain ⟨e, he⟩ := supporting_semicircle_vertical_isometry k r hr
    refine ⟨e, ?_⟩
    intro z
    rw [hpoly, ← he]
    have hrsq : r ^ 2 = 1 / (c.re - 1) ^ 2 := by
      dsimp [r]; rw [div_pow, sq_abs]; norm_num
    rw [hrsq]
    dsimp [k]
    constructor <;> intro h
    · field_simp
      have hh := congrArg (fun v : ℝ => v * (c.re - 1)) h
      nlinarith [hh, hn]
    · field_simp at h
      have hh : (c.re - 1) * ((1 - c.re) * (z.re ^ 2 + z.im ^ 2) +
          (1 + c.re) + 2 * c.im * z.re) = 0 := by nlinarith [h, hn]
      exact (mul_eq_zero.mp hh).resolve_left hd

end CurveComplex.Hyperbolic
