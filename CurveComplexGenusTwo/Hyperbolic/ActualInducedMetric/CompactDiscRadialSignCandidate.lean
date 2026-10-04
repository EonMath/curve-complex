import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactCanonicalDiscSidesCandidate

namespace CurveComplex.Hyperbolic

theorem compact_disc_circle_radial_contraction (c w : ℂ) (t : ℝ)
    (hw : Complex.normSq w < 1) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hside : 0 < Complex.normSq w - 2 * (star c * w).re + 1) :
    0 < Complex.normSq ((t : ℂ) * w) - 2 * (star c * ((t : ℂ) * w)).re + 1 := by
  have hn : Complex.normSq ((t : ℂ) * w) = t ^ 2 * Complex.normSq w := by
    rw [Complex.normSq_mul, Complex.normSq_ofReal]
    ring
  have hr : (star c * ((t : ℂ) * w)).re = t * (star c * w).re := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hn, hr]
  have hprod : 0 ≤ t * Complex.normSq w := mul_nonneg ht₀ (Complex.normSq_nonneg w)
  have htw : t * Complex.normSq w < 1 := by
    calc t * Complex.normSq w ≤ 1 * Complex.normSq w :=
      mul_le_mul_of_nonneg_right ht₁ (Complex.normSq_nonneg w)
      _ = Complex.normSq w := one_mul _
      _ < 1 := hw
  have hp : 0 ≤ (1-t) * (1-t * Complex.normSq w) :=
    mul_nonneg (by linarith) (by linarith)
  by_cases ht : t = 0
  · subst t; norm_num
  · have htpos : 0 < t := lt_of_le_of_ne ht₀ (Ne.symm ht)
    have hs : 0 < t * (Complex.normSq w - 2 * (star c * w).re + 1) :=
      mul_pos htpos hside
    nlinarith

theorem regular_hexagon_disc_side_radial_contraction (i : Fin 6) (w : ℂ) (t : ℝ)
    (hw : Complex.normSq w < 1) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hside : 0 < regularHexagonSideEquation i w) :
    0 < regularHexagonSideEquation i ((t : ℂ) * w) :=
  compact_disc_circle_radial_contraction (regularHexagonSideCenter i) w t hw ht₀ ht₁ hside

end CurveComplex.Hyperbolic
