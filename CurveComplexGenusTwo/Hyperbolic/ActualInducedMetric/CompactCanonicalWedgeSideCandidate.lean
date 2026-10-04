import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactHalfplaneJordanIdentificationCandidate

namespace CurveComplex.Hyperbolic

set_option maxHeartbeats 1000000 in
theorem regular_hexagon_first_half_wedge_side_dominates (w : ℂ)
    (hy : 0 < w.im) (hx : Real.sqrt 3 * w.im < w.re) (i : Fin 6) :
    regularHexagonSideEquation 0 w ≤ regularHexagonSideEquation i w := by
  let α := (1 + regularHexagonRadius^2)/(3*regularHexagonRadius)
  have hα : 0 < α := by dsimp [α]; exact div_pos (by positivity) (mul_pos (by norm_num) regularHexagonRadius_pos)
  have hp : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hs : (Real.sqrt 3)^2 = 3 := by norm_num
  have hxp : 0 < w.re := by nlinarith [hx,hy]
  change Complex.normSq w - 2*(star ((α:ℂ)*(idealHexagonVertex 0+idealHexagonVertex 1))*w).re+1 ≤
    Complex.normSq w - 2*(star ((α:ℂ)*(idealHexagonVertex i+idealHexagonVertex (i+1)))*w).re+1
  fin_cases i <;> norm_num [idealHexagonVertex, Complex.star_def, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im] <;>
    nlinarith [mul_pos hα hy, mul_pos hα hxp,
      mul_pos hα (sub_pos.mpr hx)]

theorem regular_hexagon_first_half_wedge_interior_iff (z : H2)
    (hy : 0 < (cayley z : ℂ).im)
    (hx : Real.sqrt 3*(cayley z : ℂ).im < (cayley z : ℂ).re) :
    z ∈ regularHexagonRegion.interior ↔ 0 < regularHexagonSideEquation 0 (cayley z : ℂ) := by
  rw [← regular_hexagon_actual_halfplane_eq_jordan_interior]
  constructor
  · intro hz; exact hz 0
  · intro h; intro i
    exact h.trans_le (regular_hexagon_first_half_wedge_side_dominates (cayley z : ℂ) hy hx i)

end CurveComplex.Hyperbolic
