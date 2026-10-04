import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactCanonicalDiscSidesCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactCanonicalCircumball

namespace CurveComplex.Hyperbolic
open Set

theorem regular_hexagon_closed_region_disc_bound (z : H2)
    (hz : z ∈ closure regularHexagonRegion.interior) :
    Complex.normSq (cayley z : ℂ) ≤ regularHexagonRadius ^ 2 := by
  let w : Metric.ball (0 : ℂ) 1 := ⟨(cayley z : ℂ), cayley_mem_ball z⟩
  have hwpos : 0 < 1 - Complex.normSq (w : ℂ) := by
    have hn : ‖(w : ℂ)‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using w.property
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (w : ℂ)]
  have hrpos : 0 < 1 - regularHexagonRadius ^ 2 := by
    nlinarith [regularHexagonRadius_pos, regularHexagonRadius_lt_one]
  have h := regularHexagon_closed_region_circumball z hz
  have hd := cayleyInverse_cosh_dist
    (⟨0, by simp only [Metric.mem_ball, dist_self]; norm_num⟩) w
  change Real.cosh (dist regularHexagonCenter (cayleyInverse w)) = _ at hd
  have hwz : cayleyInverse w = z := cayleyInverse_cayley z
  rw [hwz] at hd
  simp only [zero_sub, Complex.normSq_neg, Complex.normSq_zero, sub_zero, one_mul] at hd
  rw [hd] at h
  change 1 + 2 * Complex.normSq (w : ℂ) / (1 - Complex.normSq (w : ℂ)) ≤
    1 + 2 * regularHexagonRadius ^ 2 / (1 - regularHexagonRadius ^ 2) at h
  have hdiv : Complex.normSq (w : ℂ) / (1 - Complex.normSq (w : ℂ)) ≤
      regularHexagonRadius ^ 2 / (1 - regularHexagonRadius ^ 2) := by
    have htwo : 2 * (Complex.normSq (w : ℂ) / (1 - Complex.normSq (w : ℂ))) ≤
        2 * (regularHexagonRadius ^ 2 / (1 - regularHexagonRadius ^ 2)) := by
      simpa only [mul_div_assoc] using (le_of_add_le_add_left h)
    linarith
  have hm := (div_le_div_iff₀ hwpos hrpos).mp hdiv
  change Complex.normSq (w : ℂ) ≤ _
  nlinarith

end CurveComplex.Hyperbolic
