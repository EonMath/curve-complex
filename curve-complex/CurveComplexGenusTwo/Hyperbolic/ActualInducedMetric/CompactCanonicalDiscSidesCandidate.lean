import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactCanonicalRotationAreaCandidate

namespace CurveComplex.Hyperbolic
open Set

noncomputable def regularHexagonSideCenter (i : Fin 6) : ℂ :=
  ((1 + regularHexagonRadius ^ 2) / (3 * regularHexagonRadius) : ℝ) *
    (idealHexagonVertex i + idealHexagonVertex (i + 1))

noncomputable def regularHexagonSideEquation (i : Fin 6) (w : ℂ) : ℝ :=
  Complex.normSq w - 2 * (star (regularHexagonSideCenter i) * w).re + 1

theorem regular_hexagon_side_scale_identity :
    ((1 + regularHexagonRadius ^ 2) / (3 * regularHexagonRadius)) ^ 2 = 2 / 3 := by
  have hr : regularHexagonRadius ≠ 0 := regularHexagonRadius_pos.ne'
  have hs : (Real.sqrt 3) ^ 2 = 3 := by norm_num
  have h := regularHexagonRadius_sq
  field_simp
  nlinarith [h, hs]

theorem regular_hexagon_side_center_normSq (i : Fin 6) :
    Complex.normSq (regularHexagonSideCenter i) = 2 := by
  rw [regularHexagonSideCenter, Complex.normSq_mul, Complex.normSq_ofReal,
    Complex.normSq_add, idealHexagonVertex_normSq, idealHexagonVertex_normSq]
  have h := idealHexagon_adjacent_inner_re i
  have h' : (idealHexagonVertex i * (starRingEnd ℂ) (idealHexagonVertex (i + 1))).re = 1 / 2 := by
    simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im] at h ⊢
    nlinarith
  rw [h', ← pow_two, regular_hexagon_side_scale_identity]
  norm_num

theorem regular_hexagon_side_equation_circle (i : Fin 6) (w : ℂ) :
    regularHexagonSideEquation i w = Complex.normSq (w - regularHexagonSideCenter i) - 1 := by
  rw [Complex.normSq_sub, regular_hexagon_side_center_normSq]
  simp [regularHexagonSideEquation, Complex.normSq_apply, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  ring

theorem regular_hexagon_side_equation_origin (i : Fin 6) :
    regularHexagonSideEquation i 0 = 1 := by simp [regularHexagonSideEquation]

theorem regular_hexagon_side_equation_left_vertex (i : Fin 6) :
    regularHexagonSideEquation i (regularHexagonDiscPoint i) = 0 := by
  have hr : regularHexagonRadius ≠ 0 := regularHexagonRadius_pos.ne'
  have hnorm := idealHexagonVertex_normSq i
  have hinner := idealHexagon_adjacent_inner_re i
  have hrev : (star (idealHexagonVertex (i + 1)) * idealHexagonVertex i).re = 1 / 2 := by
    simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im] at hinner ⊢
    nlinarith
  have hself : (star (idealHexagonVertex i) * idealHexagonVertex i).re = 1 := by
    simpa [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.normSq_apply] using hnorm
  unfold regularHexagonSideEquation regularHexagonSideCenter regularHexagonDiscPoint
  rw [Complex.normSq_mul, Complex.normSq_ofReal, idealHexagonVertex_normSq]
  simp only [star_mul', Complex.star_def, Complex.conj_ofReal, map_add, mul_add, add_mul,
    Complex.add_re]
  have hfactor (z : ℂ) :
      (((((1 + regularHexagonRadius ^ 2) / (3 * regularHexagonRadius) : ℝ) : ℂ) * z) *
        (regularHexagonRadius * idealHexagonVertex i)).re =
      ((1 + regularHexagonRadius ^ 2) / (3 * regularHexagonRadius)) *
        regularHexagonRadius * (z * idealHexagonVertex i).re := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  simp only [map_mul, Complex.conj_ofReal]
  simp_rw [hfactor]
  change regularHexagonRadius * regularHexagonRadius * 1 -
    (2 * (((1 + regularHexagonRadius ^ 2) / (3 * regularHexagonRadius)) * regularHexagonRadius *
      (star (idealHexagonVertex i) * idealHexagonVertex i).re) +
    2 * (((1 + regularHexagonRadius ^ 2) / (3 * regularHexagonRadius)) * regularHexagonRadius *
      (star (idealHexagonVertex (i + 1)) * idealHexagonVertex i).re)) + 1 = 0
  rw [hself, hrev]
  field_simp
  ring

theorem regular_hexagon_side_equation_right_vertex (i : Fin 6) :
    regularHexagonSideEquation i (regularHexagonDiscPoint (i + 1)) = 0 := by
  have hr : regularHexagonRadius ≠ 0 := regularHexagonRadius_pos.ne'
  have hnorm := idealHexagonVertex_normSq (i + 1)
  have hinner := idealHexagon_adjacent_inner_re i
  unfold regularHexagonSideEquation regularHexagonSideCenter regularHexagonDiscPoint
  simp only [Complex.normSq_mul, Complex.normSq_ofReal, idealHexagonVertex_normSq,
    Complex.normSq_apply, Complex.star_def, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.add_im, zero_mul, mul_zero, add_zero, sub_zero]
  simp only [Complex.normSq_apply] at hnorm
  simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im] at hinner
  field_simp
  nlinarith [hnorm, hinner]

end CurveComplex.Hyperbolic
