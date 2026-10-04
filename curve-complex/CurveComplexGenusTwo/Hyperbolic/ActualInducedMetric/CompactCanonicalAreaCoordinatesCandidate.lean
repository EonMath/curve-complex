import CurveComplexGenusTwo.Hyperbolic.CompactHexagonRegion
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactVertexGeodesics

namespace CurveComplex.Hyperbolic

set_option maxHeartbeats 1000000 in
theorem regular_hexagon_radial_height_exact :
    (1 + regularHexagonRadius) / (1 - regularHexagonRadius) = Real.sqrt 3 + Real.sqrt 2 := by
  let r := regularHexagonRadius
  let t := (1 + r) / (1 - r)
  have hrpos : 0 < r := regularHexagonRadius_pos
  have hrlt : r < 1 := regularHexagonRadius_lt_one
  have hrsq : r ^ 2 = 2 - Real.sqrt 3 := regularHexagonRadius_sq
  have hs₃ : (Real.sqrt 3) ^ 2 = 3 := by norm_num
  have hs₂ : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hp₃ : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hp₂ : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hden : 1 - r ≠ 0 := by linarith
  have htquad : t ^ 2 - 2 * Real.sqrt 3 * t + 1 = 0 := by
    dsimp [t]
    field_simp
    nlinarith [hs₃, hrsq]
  have hs₃lt : Real.sqrt 3 < 7 / 4 := by nlinarith [hs₃]
  have hrhalf : 1 / 2 < r := by
    by_contra h
    have hsq := (sq_le_sq₀ hrpos.le (by norm_num : 0 ≤ (1 / 2 : ℝ))).mpr (le_of_not_gt h)
    nlinarith [hs₃lt, hrsq]
  have htbig : 3 < t := by
    dsimp [t]
    apply (lt_div_iff₀ (by linarith)).mpr
    linarith
  have hdiff : 0 ≤ t - Real.sqrt 3 := by nlinarith [hs₃]
  have hs : (t - Real.sqrt 3) ^ 2 = 2 := by nlinarith [htquad, hs₃]
  have heq : t - Real.sqrt 3 = Real.sqrt 2 := by nlinarith [hs₂]
  change t = _
  linarith

theorem regular_hexagon_vertex_zero_coordinates :
    (regularHexagonCandidate.vertex 0).re = 0 ∧
    (regularHexagonCandidate.vertex 0).im = Real.sqrt 3 + Real.sqrt 2 := by
  have hre : (regularHexagonCandidate.vertex 0).re = 0 := by
    change (cayleyInverse ⟨regularHexagonDiscPoint 0, _⟩).re = 0
    rw [cayleyInverse_re]
    simp [regularHexagonDiscPoint, idealHexagonVertex]
  refine ⟨hre, ?_⟩
  change (cayleyInverse ⟨regularHexagonDiscPoint 0, _⟩).im = _
  rw [cayleyInverse_im]
  have hrne : 1 - regularHexagonRadius ≠ 0 := by
    linarith [regularHexagonRadius_lt_one]
  have heq : (1 - Complex.normSq (regularHexagonDiscPoint 0)) /
      Complex.normSq (1 - regularHexagonDiscPoint 0) =
      (1 + regularHexagonRadius) / (1 - regularHexagonRadius) := by
    simp only [regularHexagonDiscPoint, idealHexagonVertex, mul_one,
      Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    field_simp
    ring
  rw [heq, regular_hexagon_radial_height_exact]

end CurveComplex.Hyperbolic
