import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactUnitSemicircleParam
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactVertexCircumballAlgebra

namespace CurveComplex.Hyperbolic
open Set Topology

theorem occupied_quarter_horizontal_sign (c p : H2)
    (hp : p.re = 0) (hi : p.im = 1) (r : ℝ) (hr : 0 < r)
    (positive inner : Bool)
    (hbound : ∀ z ∈ Metric.ball p r ∩ {w : H2 |
      (if positive then 0 < w.re else w.re < 0) ∧
      (if inner then w.re ^ 2 + w.im ^ 2 < 1 else 1 < w.re ^ 2 + w.im ^ 2)},
      Real.cosh (dist c z) ≤ Real.cosh (dist c p)) :
    if positive then 0 < c.re else c.re < 0 := by
  obtain ⟨z, hz, hn, hs⟩ := unit_circle_point_of_either_sign_in_ball p hp hi r hr positive
  let Q : Set H2 := Metric.ball p r ∩ {w : H2 |
    (if positive then 0 < w.re else w.re < 0) ∧
    (if inner then w.re ^ 2 + w.im ^ 2 < 1 else 1 < w.re ^ 2 + w.im ^ 2)}
  have hcl : z ∈ closure Q := by
    cases inner
    · exact unit_circle_mem_closure_outer_quarter p z r positive
        (by rw [hp, hi]; norm_num) hz hs hn
    · exact unit_circle_mem_closure_inner_quarter p z r positive hz hs hn
  have hclosed : IsClosed {w : H2 |
      Real.cosh (dist c w) ≤ Real.cosh (dist c p)} :=
    isClosed_le (Real.continuous_cosh.comp (continuous_const.dist continuous_id)) continuous_const
  have hc : Real.cosh (dist c z) ≤ Real.cosh (dist c p) :=
    closure_minimal hbound hclosed hcl
  have hf := (normalized_circumball_sublevel c p z hp hi).mp hc
  have hzim : z.im < 1 := by
    cases positive
    · change z.re < 0 at hs
      nlinarith [z.im_pos, sq_pos_of_ne_zero (ne_of_lt hs)]
    · change 0 < z.re at hs
      nlinarith [z.im_pos, sq_pos_of_ne_zero (ne_of_gt hs)]
  have hN : 0 < 1 + c.re ^ 2 + c.im ^ 2 := by positivity
  cases positive
  · change c.re < 0
    change z.re < 0 at hs
    by_contra h
    have hc0 : 0 ≤ c.re := le_of_not_gt h
    have hm : c.re * z.re ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc0 hs.le
    nlinarith [mul_pos hN (sub_pos.mpr hzim)]
  · change 0 < c.re
    change 0 < z.re at hs
    by_contra h
    have hc0 : c.re ≤ 0 := le_of_not_gt h
    have hm : c.re * z.re ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc0 hs.le
    nlinarith [mul_pos hN (sub_pos.mpr hzim)]

theorem occupied_quarter_vertical_sign (c p : H2)
    (hp : p.re = 0) (hi : p.im = 1) (r : ℝ) (hr : 0 < r)
    (positive inner : Bool)
    (hbound : ∀ z ∈ Metric.ball p r ∩ {w : H2 |
      (if positive then 0 < w.re else w.re < 0) ∧
      (if inner then w.re ^ 2 + w.im ^ 2 < 1 else 1 < w.re ^ 2 + w.im ^ 2)},
      Real.cosh (dist c z) ≤ Real.cosh (dist c p)) :
    if inner then c.re ^ 2 + c.im ^ 2 < 1 else 1 < c.re ^ 2 + c.im ^ 2 := by
  obtain ⟨z, hz, hs, hn⟩ := vertical_axis_point_of_either_side_in_ball p hp hi r hr inner
  let Q : Set H2 := Metric.ball p r ∩ {w : H2 |
    (if positive then 0 < w.re else w.re < 0) ∧
    (if inner then w.re ^ 2 + w.im ^ 2 < 1 else 1 < w.re ^ 2 + w.im ^ 2)}
  have hnorm : if inner then z.re ^ 2 + z.im ^ 2 < 1 else 1 < z.re ^ 2 + z.im ^ 2 := by
    rw [hs]
    cases inner
    · change 1 < z.im at hn
      change 1 < 0 ^ 2 + z.im ^ 2
      nlinarith [z.im_pos]
    · change z.im < 1 at hn
      change 0 ^ 2 + z.im ^ 2 < 1
      nlinarith [z.im_pos]
  have hcl : z ∈ closure Q := vertical_axis_mem_closure_quarter p z r positive inner hz hs hnorm
  have hclosed : IsClosed {w : H2 |
      Real.cosh (dist c w) ≤ Real.cosh (dist c p)} :=
    isClosed_le (Real.continuous_cosh.comp (continuous_const.dist continuous_id)) continuous_const
  have hc : Real.cosh (dist c z) ≤ Real.cosh (dist c p) :=
    closure_minimal hbound hclosed hcl
  have hf := (normalized_circumball_sublevel c p z hp hi).mp hc
  rw [hs] at hf
  cases inner
  · change 1 < c.re ^ 2 + c.im ^ 2
    change 1 < z.im at hn
    by_contra h
    have hN : c.re ^ 2 + c.im ^ 2 ≤ 1 := le_of_not_gt h
    have hm := mul_pos (sub_pos.mpr hn)
      (show 0 < z.im - (c.re ^ 2 + c.im ^ 2) by linarith)
    nlinarith [hm]
  · change c.re ^ 2 + c.im ^ 2 < 1
    change z.im < 1 at hn
    by_contra h
    have hN : 1 ≤ c.re ^ 2 + c.im ^ 2 := le_of_not_gt h
    have hm := mul_pos (show 0 < 1 - z.im by linarith)
      (show 0 < c.re ^ 2 + c.im ^ 2 - z.im by linarith)
    nlinarith [hm]

end CurveComplex.Hyperbolic
