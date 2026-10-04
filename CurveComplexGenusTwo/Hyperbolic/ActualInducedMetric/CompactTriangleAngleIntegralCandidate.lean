import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactArcsineIntegralCandidate

namespace CurveComplex.Hyperbolic

 theorem arcsine_orthogonal_circle_difference {x y : ℝ}
    (hx : 0 ≤ x) (hy : y ≤ 0) (hcircle : x ^ 2 + y ^ 2 = 1) :
    Real.arcsin y - Real.arcsin x = -(Real.pi / 2) := by
  have hsqrt : Real.sqrt (1 - x ^ 2) = -y := by
    apply (Real.sqrt_eq_iff_eq_sq (by nlinarith [sq_nonneg y]) (by linarith)).mpr
    nlinarith
  have hsin : Real.sin (Real.arcsin x - Real.pi / 2) = y := by
    rw [Real.sin_sub, Real.cos_pi_div_two, Real.sin_pi_div_two,
      mul_zero, mul_one, zero_sub, Real.cos_arcsin, hsqrt, neg_neg]
  have hlo : -(Real.pi / 2) ≤ Real.arcsin x - Real.pi / 2 := by
    have h := Real.arcsin_nonneg.mpr hx
    linarith
  have hhi : Real.arcsin x - Real.pi / 2 ≤ Real.pi / 2 := by
    have h := Real.arcsin_le_pi_div_two x
    linarith [Real.pi_pos]
  have ha := Real.arcsin_sin hlo hhi
  rw [hsin] at ha
  linarith

set_option maxHeartbeats 1000000 in
theorem compact_right_triangle_arcsine_value :
    let t := Real.sqrt 3 + Real.sqrt 2
    let a := -(Real.sqrt 3 + 2 * Real.sqrt 2) / 5
    (Real.arcsin (Real.sqrt 3 / 2) - Real.arcsin ((a + Real.sqrt 3) / 2)) -
      (Real.arcsin (-1 / Real.sqrt 2) - Real.arcsin ((a - t) / (Real.sqrt 2 * t))) =
        Real.pi / 12 := by
  dsimp only
  let t := Real.sqrt 3 + Real.sqrt 2
  let a := -(Real.sqrt 3 + 2 * Real.sqrt 2) / 5
  have hs₃ : (Real.sqrt 3) ^ 2 = 3 := by norm_num
  have hs₂ : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hp₃ : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hp₂ : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have ht : 0 < t := by dsimp [t]; positivity
  have hxy : ((a + Real.sqrt 3) / 2) ^ 2 +
      ((a - t) / (Real.sqrt 2 * t)) ^ 2 = 1 := by
    dsimp [a, t]
    field_simp
    have h₂₃ : (Real.sqrt 2) ^ 3 = 2 * Real.sqrt 2 := by
      calc _ = (Real.sqrt 2) ^ 2 * Real.sqrt 2 := by ring
           _ = _ := by rw [hs₂]
    have h₂₄ : (Real.sqrt 2) ^ 4 = 4 := by
      calc _ = ((Real.sqrt 2) ^ 2) ^ 2 := by ring
           _ = _ := by rw [hs₂]; norm_num
    have h₂₅ : (Real.sqrt 2) ^ 5 = 4 * Real.sqrt 2 := by
      calc _ = (Real.sqrt 2) ^ 4 * Real.sqrt 2 := by ring
           _ = _ := by rw [h₂₄]
    have h₂₆ : (Real.sqrt 2) ^ 6 = 8 := by
      calc _ = ((Real.sqrt 2) ^ 2) ^ 3 := by ring
           _ = _ := by rw [hs₂]; norm_num
    have h₃₃ : (Real.sqrt 3) ^ 3 = 3 * Real.sqrt 3 := by
      calc _ = (Real.sqrt 3) ^ 2 * Real.sqrt 3 := by ring
           _ = _ := by rw [hs₃]
    have h₃₄ : (Real.sqrt 3) ^ 4 = 9 := by
      calc _ = ((Real.sqrt 3) ^ 2) ^ 2 := by ring
           _ = _ := by rw [hs₃]; norm_num
    ring_nf
    rw [hs₃, hs₂, h₂₃, h₂₄, h₂₅, h₂₆, h₃₃, h₃₄]
    ring
  have hx : 0 ≤ (a + Real.sqrt 3) / 2 := by
    dsimp [a]; nlinarith
  have hy : (a - t) / (Real.sqrt 2 * t) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · dsimp [a, t]; linarith
    · positivity
  have harc := arcsine_orthogonal_circle_difference hx hy hxy
  have h₃ : Real.arcsin (Real.sqrt 3 / 2) = Real.pi / 3 := by
    rw [← Real.sin_pi_div_three]
    apply Real.arcsin_sin <;> linarith [Real.pi_pos]
  have h₂ : Real.arcsin (-1 / Real.sqrt 2) = -(Real.pi / 4) := by
    have heq : -1 / Real.sqrt 2 = -(Real.sqrt 2 / 2) := by
      field_simp; nlinarith
    rw [heq, Real.arcsin_neg, ← Real.sin_pi_div_four]
    congr 1
    apply Real.arcsin_sin <;> linarith [Real.pi_pos]
  change (Real.arcsin (Real.sqrt 3 / 2) - Real.arcsin ((a + Real.sqrt 3) / 2)) -
    (Real.arcsin (-1 / Real.sqrt 2) - Real.arcsin ((a - t) / (Real.sqrt 2 * t))) = _
  rw [h₃, h₂]
  linarith

end CurveComplex.Hyperbolic
