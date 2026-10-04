import CurveComplexGenusTwo.Hyperbolic.HexagonMetric

namespace CurveComplex.Hyperbolic

noncomputable def semicircleCentre (p q : H2) : ℝ :=
  (Complex.normSq (q : ℂ) - Complex.normSq (p : ℂ)) /
    (2 * ((q : ℂ).re - (p : ℂ).re))

noncomputable def geodesicTangent (p q : H2) : ℂ :=
  if (p : ℂ).re = (q : ℂ).re then Complex.I
  else Complex.I * ((p : ℂ) - (semicircleCentre p q : ℂ))

def IsRightAngle (q p r : H2) : Prop :=
  (star (geodesicTangent p q) * geodesicTangent p r).re = 0

private theorem tangent_dot (p q r : H2)
    (hq : (p : ℂ).re ≠ (q : ℂ).re)
    (hr : (p : ℂ).re ≠ (r : ℂ).re) :
    IsRightAngle q p r ↔
      ((p : ℂ).re - semicircleCentre p q) *
        ((p : ℂ).re - semicircleCentre p r) + (p : ℂ).im ^ 2 = 0 := by
  simp only [IsRightAngle, geodesicTangent, if_neg hq, if_neg hr,
    star_mul', star_sub, Complex.star_def, Complex.conj_I,
    Complex.conj_ofReal,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
    Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem rightAngle_of_circle_polynomial (p q r : H2)
    (hq : (p : ℂ).re ≠ (q : ℂ).re)
    (hr : (p : ℂ).re ≠ (r : ℂ).re)
    (h :
      ((p : ℂ).im ^ 2 - (q : ℂ).im ^ 2 -
          ((q : ℂ).re - (p : ℂ).re) ^ 2) *
        ((p : ℂ).im ^ 2 - (r : ℂ).im ^ 2 -
          ((r : ℂ).re - (p : ℂ).re) ^ 2) +
        4 * (p : ℂ).im ^ 2 *
          ((q : ℂ).re - (p : ℂ).re) *
          ((r : ℂ).re - (p : ℂ).re) = 0) :
    IsRightAngle q p r := by
  rw [tangent_dot p q r hq hr]
  have hq' : (q : ℂ).re - (p : ℂ).re ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  have hr' : (r : ℂ).re - (p : ℂ).re ≠ 0 := sub_ne_zero.mpr (Ne.symm hr)
  unfold semicircleCentre
  simp only [Complex.normSq_apply]
  field_simp
  nlinarith [h]

private theorem radius_algebra :
    regularHexagonRadius ^ 4 - 4 * regularHexagonRadius ^ 2 + 1 = 0 := by
  rw [show regularHexagonRadius ^ 4 = (regularHexagonRadius ^ 2) ^ 2 by ring]
  rw [regularHexagonRadius_sq]
  nlinarith [show (Real.sqrt 3) ^ 2 = 3 by norm_num]

private theorem point_re (i : Fin 6) :
    (regularHexagonH2Point i : ℂ).re =
      -2 * (regularHexagonDiscPoint i).im /
        Complex.normSq (1 - regularHexagonDiscPoint i) := by
  exact cayleyInverse_re
    ⟨regularHexagonDiscPoint i, regularHexagonDiscPoint_mem_ball i⟩

private theorem point_im (i : Fin 6) :
    (regularHexagonH2Point i : ℂ).im =
      (1 - Complex.normSq (regularHexagonDiscPoint i)) /
        Complex.normSq (1 - regularHexagonDiscPoint i) := by
  exact cayleyInverse_im
    ⟨regularHexagonDiscPoint i, regularHexagonDiscPoint_mem_ball i⟩

private theorem point_denom_pos (i : Fin 6) :
    0 < Complex.normSq (1 - regularHexagonDiscPoint i) := by
  rw [Complex.normSq_pos]
  exact one_sub_ball_ne_zero
    ⟨regularHexagonDiscPoint i, regularHexagonDiscPoint_mem_ball i⟩

private noncomputable def vertexDenom (i : Fin 6) : ℝ :=
  1 - 2 * regularHexagonRadius * (idealHexagonVertex i).re +
    regularHexagonRadius ^ 2

private theorem vertexDenom_eq (i : Fin 6) :
    vertexDenom i = Complex.normSq (1 - regularHexagonDiscPoint i) := by
  have hnorm := idealHexagonVertex_normSq i
  rw [Complex.normSq_apply] at hnorm
  simp only [vertexDenom, regularHexagonDiscPoint, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero, zero_sub]
  nlinarith [mul_nonneg (sq_nonneg regularHexagonRadius)
    (sq_nonneg (idealHexagonVertex i).re)]

private theorem vertexDenom_pos (i : Fin 6) : 0 < vertexDenom i := by
  rw [vertexDenom_eq]
  exact point_denom_pos i

private theorem vertex_re (i : Fin 6) :
    (regularHexagonH2Point i : ℂ).re =
      -2 * regularHexagonRadius * (idealHexagonVertex i).im /
        vertexDenom i := by
  rw [point_re, vertexDenom_eq]
  simp [regularHexagonDiscPoint, Complex.mul_im]
  ring

private theorem vertex_im (i : Fin 6) :
    (regularHexagonH2Point i : ℂ).im =
      (1 - regularHexagonRadius ^ 2) / vertexDenom i := by
  rw [point_im, vertexDenom_eq]
  have hi := idealHexagonVertex_normSq i
  rw [regularHexagonDiscPoint, Complex.normSq_mul, hi]
  simp [Complex.normSq_ofReal]
  ring

private theorem prev_index (i : Fin 6) :
    i - 1 = match i with
      | 0 => 5 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 4 := by
  fin_cases i <;> decide

private theorem next_index (i : Fin 6) :
    i + 1 = match i with
      | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 5 | 5 => 0 := by
  fin_cases i <;> decide

private theorem denom0_pos :
    0 < 1 - 2 * regularHexagonRadius + regularHexagonRadius ^ 2 := by
  simpa [vertexDenom, idealHexagonVertex] using vertexDenom_pos 0

private theorem denom1_pos :
    0 < 1 - regularHexagonRadius + regularHexagonRadius ^ 2 := by
  convert vertexDenom_pos 1 using 1
  norm_num [vertexDenom, idealHexagonVertex]
  ring

private theorem denom2_pos :
    0 < 1 + regularHexagonRadius + regularHexagonRadius ^ 2 := by
  convert vertexDenom_pos 2 using 1
  norm_num [vertexDenom, idealHexagonVertex]
  ring

private theorem denom3_pos :
    0 < 1 + 2 * regularHexagonRadius + regularHexagonRadius ^ 2 := by
  simpa [vertexDenom, idealHexagonVertex] using vertexDenom_pos 3

private theorem vertex_re_0 : (regularHexagonH2Point 0 : ℂ).re = 0 := by
  rw [vertex_re]
  norm_num [idealHexagonVertex]

private theorem vertex_re_1 :
    (regularHexagonH2Point 1 : ℂ).re =
      -(regularHexagonRadius * Real.sqrt 3) /
        (1 - regularHexagonRadius + regularHexagonRadius ^ 2) := by
  rw [vertex_re]
  norm_num [vertexDenom, idealHexagonVertex]
  congr 1 <;> ring

private theorem vertex_re_2 :
    (regularHexagonH2Point 2 : ℂ).re =
      -(regularHexagonRadius * Real.sqrt 3) /
        (1 + regularHexagonRadius + regularHexagonRadius ^ 2) := by
  rw [vertex_re]
  norm_num [vertexDenom, idealHexagonVertex]
  congr 1 <;> ring

private theorem vertex_re_3 : (regularHexagonH2Point 3 : ℂ).re = 0 := by
  rw [vertex_re]
  norm_num [idealHexagonVertex]

private theorem vertex_re_4 :
    (regularHexagonH2Point 4 : ℂ).re =
      regularHexagonRadius * Real.sqrt 3 /
        (1 + regularHexagonRadius + regularHexagonRadius ^ 2) := by
  rw [vertex_re]
  norm_num [vertexDenom, idealHexagonVertex]
  congr 1 <;> ring

private theorem vertex_re_5 :
    (regularHexagonH2Point 5 : ℂ).re =
      regularHexagonRadius * Real.sqrt 3 /
        (1 - regularHexagonRadius + regularHexagonRadius ^ 2) := by
  rw [vertex_re]
  norm_num [vertexDenom, idealHexagonVertex]
  congr 1 <;> ring

private theorem re_num_pos :
    0 < regularHexagonRadius * Real.sqrt 3 := by
  exact mul_pos regularHexagonRadius_pos (Real.sqrt_pos.2 (by norm_num))

private theorem denom1_lt_denom2 :
    1 - regularHexagonRadius + regularHexagonRadius ^ 2 <
      1 + regularHexagonRadius + regularHexagonRadius ^ 2 := by
  linarith [regularHexagonRadius_pos]

private theorem vertex_re_1_lt_2 :
    (regularHexagonH2Point 1 : ℂ).re <
      (regularHexagonH2Point 2 : ℂ).re := by
  rw [vertex_re_1, vertex_re_2]
  rw [neg_div, neg_div]
  apply neg_lt_neg
  apply (div_lt_div_iff₀ denom2_pos denom1_pos).2
  nlinarith [mul_pos re_num_pos (sub_pos.mpr denom1_lt_denom2)]

private theorem vertex_re_2_lt_0 :
    (regularHexagonH2Point 2 : ℂ).re < 0 := by
  rw [vertex_re_2]
  rw [neg_div]
  exact neg_neg_of_pos (div_pos re_num_pos denom2_pos)

private theorem vertex_re_0_lt_4 :
    0 < (regularHexagonH2Point 4 : ℂ).re := by
  rw [vertex_re_4]
  exact div_pos re_num_pos denom2_pos

private theorem vertex_re_4_lt_5 :
    (regularHexagonH2Point 4 : ℂ).re <
      (regularHexagonH2Point 5 : ℂ).re := by
  rw [vertex_re_4, vertex_re_5]
  apply (div_lt_div_iff₀ denom2_pos denom1_pos).2
  nlinarith [mul_pos re_num_pos (sub_pos.mpr denom1_lt_denom2)]

theorem regularHexagonCandidate_right_angles (i : Fin 6) :
    IsRightAngle (regularHexagonCandidate.vertex (i - 1))
      (regularHexagonCandidate.vertex i)
      (regularHexagonCandidate.vertex (i + 1)) := by
  have hx10 : (regularHexagonH2Point 1 : ℂ).re <
      (regularHexagonH2Point 0 : ℂ).re := by
    rw [vertex_re_0]
    exact lt_trans vertex_re_1_lt_2 vertex_re_2_lt_0
  have hx23 : (regularHexagonH2Point 2 : ℂ).re <
      (regularHexagonH2Point 3 : ℂ).re := by
    rw [vertex_re_3]
    exact vertex_re_2_lt_0
  have hx34 : (regularHexagonH2Point 3 : ℂ).re <
      (regularHexagonH2Point 4 : ℂ).re := by
    rw [vertex_re_3]
    exact vertex_re_0_lt_4
  have hx05 : (regularHexagonH2Point 0 : ℂ).re <
      (regularHexagonH2Point 5 : ℂ).re := by
    rw [vertex_re_0]
    exact lt_trans vertex_re_0_lt_4 vertex_re_4_lt_5
  change IsRightAngle (regularHexagonH2Point (i - 1))
    (regularHexagonH2Point i) (regularHexagonH2Point (i + 1))
  rw [prev_index, next_index]
  fin_cases i
  · dsimp
    have hD0 : 0 < 1 - 2 * regularHexagonRadius + regularHexagonRadius ^ 2 := by
      simpa [vertexDenom, idealHexagonVertex] using vertexDenom_pos 0
    have hD1 : 0 < 1 - regularHexagonRadius + regularHexagonRadius ^ 2 := by
      convert vertexDenom_pos 1 using 1
      norm_num [vertexDenom, idealHexagonVertex]
      ring
    have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    have hr := regularHexagonRadius_pos
    have hnum : 0 < 2 * regularHexagonRadius * (Real.sqrt 3 / 2) := by positivity
    apply rightAngle_of_circle_polynomial
    · simp only [vertex_re]
      norm_num [vertexDenom, idealHexagonVertex]
      rw [show 1 - 2 * regularHexagonRadius * (1 / 2) + regularHexagonRadius ^ 2 =
        1 - regularHexagonRadius + regularHexagonRadius ^ 2 by ring]
      exact ne_of_lt (div_pos hnum hD1)
    · simp only [vertex_re]
      norm_num [vertexDenom, idealHexagonVertex]
      rw [show 1 - 2 * regularHexagonRadius * (1 / 2) + regularHexagonRadius ^ 2 =
        1 - regularHexagonRadius + regularHexagonRadius ^ 2 by ring]
      rw [neg_div]
      exact Ne.symm (ne_of_lt (neg_neg_of_pos
        (div_pos hnum hD1)))
    · simp only [vertex_re, vertex_im]
      norm_num [vertexDenom, idealHexagonVertex]
      rw [show 1 - 2 * regularHexagonRadius * (1 / 2) + regularHexagonRadius ^ 2 =
        1 - regularHexagonRadius + regularHexagonRadius ^ 2 by ring]
      have hD0' : 1 - regularHexagonRadius * 2 + regularHexagonRadius ^ 2 ≠ 0 := by
        convert hD0.ne' using 1 <;> ring
      field_simp [hD0.ne', hD0', hD1.ne']
      rw [show (Real.sqrt 3) ^ 2 = 3 by norm_num]
      linear_combination
        (-8 * regularHexagonRadius ^ 2 *
          (1 - regularHexagonRadius + regularHexagonRadius ^ 2) ^ 2 *
          (1 - 2 * regularHexagonRadius + regularHexagonRadius ^ 2) ^ 2) *
          radius_algebra
  · dsimp
    apply rightAngle_of_circle_polynomial
    · exact ne_of_lt hx10
    · exact ne_of_lt vertex_re_1_lt_2
    · simp only [vertex_re, vertex_im]
      norm_num [vertexDenom, idealHexagonVertex]
      field_simp [denom0_pos.ne', denom1_pos.ne', denom2_pos.ne']
      have hD0' : 1 - regularHexagonRadius * 2 + regularHexagonRadius ^ 2 ≠ 0 := by
        convert denom0_pos.ne' using 1 <;> ring
      field_simp [hD0']
      rw [show (Real.sqrt 3) ^ 2 = 3 by norm_num]
      linear_combination
        (-8 * regularHexagonRadius ^ 2 *
          (1 - regularHexagonRadius + regularHexagonRadius ^ 2) ^ 2 *
          (1 + regularHexagonRadius + regularHexagonRadius ^ 2) *
          (1 - 2 * regularHexagonRadius + regularHexagonRadius ^ 2)) *
          radius_algebra
  · dsimp
    apply rightAngle_of_circle_polynomial
    · exact Ne.symm (ne_of_lt vertex_re_1_lt_2)
    · exact ne_of_lt hx23
    · simp only [vertex_re, vertex_im]
      norm_num [vertexDenom, idealHexagonVertex]
      field_simp [denom1_pos.ne', denom2_pos.ne', denom3_pos.ne']
      have hD3' : 1 + regularHexagonRadius * 2 + regularHexagonRadius ^ 2 ≠ 0 := by
        convert denom3_pos.ne' using 1 <;> ring
      field_simp [hD3']
      rw [show (Real.sqrt 3) ^ 2 = 3 by norm_num]
      linear_combination
        (-8 * regularHexagonRadius ^ 2 *
          (1 - regularHexagonRadius + regularHexagonRadius ^ 2) *
          (1 + regularHexagonRadius + regularHexagonRadius ^ 2) ^ 2 *
          (1 + 2 * regularHexagonRadius + regularHexagonRadius ^ 2)) *
          radius_algebra
  · dsimp
    apply rightAngle_of_circle_polynomial
    · exact Ne.symm (ne_of_lt hx23)
    · exact ne_of_lt hx34
    · simp only [vertex_re, vertex_im]
      norm_num [vertexDenom, idealHexagonVertex]
      field_simp [denom2_pos.ne', denom3_pos.ne']
      have hD3' : 1 + regularHexagonRadius * 2 + regularHexagonRadius ^ 2 ≠ 0 := by
        convert denom3_pos.ne' using 1 <;> ring
      field_simp [hD3']
      rw [show (Real.sqrt 3) ^ 2 = 3 by norm_num]
      linear_combination
        (-8 * regularHexagonRadius ^ 2 *
          (1 + regularHexagonRadius + regularHexagonRadius ^ 2) ^ 2 *
          (1 + 2 * regularHexagonRadius + regularHexagonRadius ^ 2) ^ 2) *
          radius_algebra
  · dsimp
    apply rightAngle_of_circle_polynomial
    · exact Ne.symm (ne_of_lt hx34)
    · exact ne_of_lt vertex_re_4_lt_5
    · simp only [vertex_re, vertex_im]
      norm_num [vertexDenom, idealHexagonVertex]
      field_simp [denom1_pos.ne', denom2_pos.ne', denom3_pos.ne']
      have hD3' : 1 + regularHexagonRadius * 2 + regularHexagonRadius ^ 2 ≠ 0 := by
        convert denom3_pos.ne' using 1 <;> ring
      field_simp [hD3']
      rw [show (Real.sqrt 3) ^ 2 = 3 by norm_num]
      linear_combination
        (-8 * regularHexagonRadius ^ 2 *
          (1 - regularHexagonRadius + regularHexagonRadius ^ 2) *
          (1 + regularHexagonRadius + regularHexagonRadius ^ 2) ^ 2 *
          (1 + 2 * regularHexagonRadius + regularHexagonRadius ^ 2)) *
          radius_algebra
  · dsimp
    apply rightAngle_of_circle_polynomial
    · exact Ne.symm (ne_of_lt vertex_re_4_lt_5)
    · exact Ne.symm (ne_of_lt hx05)
    · simp only [vertex_re, vertex_im]
      norm_num [vertexDenom, idealHexagonVertex]
      field_simp [denom0_pos.ne', denom1_pos.ne', denom2_pos.ne']
      have hD0' : 1 - regularHexagonRadius * 2 + regularHexagonRadius ^ 2 ≠ 0 := by
        convert denom0_pos.ne' using 1 <;> ring
      field_simp [hD0']
      rw [show (Real.sqrt 3) ^ 2 = 3 by norm_num]
      linear_combination
        (-8 * regularHexagonRadius ^ 2 *
          (1 - regularHexagonRadius + regularHexagonRadius ^ 2) ^ 2 *
          (1 + regularHexagonRadius + regularHexagonRadius ^ 2) *
          (1 - 2 * regularHexagonRadius + regularHexagonRadius ^ 2)) *
          radius_algebra

theorem Hexagon.edges_disjoint_of_cross_sum_gt (P : Hexagon) (i j : Fin 6)
    (hcross :
      dist (P.vertex i) (P.vertex j) +
        dist (P.vertex (i + 1)) (P.vertex (j + 1)) >
      dist (P.vertex i) (P.vertex (i + 1)) +
        dist (P.vertex j) (P.vertex (j + 1))) :
    Disjoint (P.edge i) (P.edge j) := by
  rw [Set.disjoint_left]
  intro z hzi hzj
  have hi : dist (P.vertex i) z + dist z (P.vertex (i + 1)) =
      dist (P.vertex i) (P.vertex (i + 1)) := hzi
  have hj : dist (P.vertex j) z + dist z (P.vertex (j + 1)) =
      dist (P.vertex j) (P.vertex (j + 1)) := hzj
  have h1 := dist_triangle (P.vertex i) z (P.vertex j)
  have h2 := dist_triangle (P.vertex (i + 1)) z (P.vertex (j + 1))
  rw [dist_comm z (P.vertex j)] at h1
  rw [dist_comm (P.vertex (i + 1)) z] at h2
  linarith

end CurveComplex.Hyperbolic
