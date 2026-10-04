import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactDiscRadialSignCandidate

namespace CurveComplex.Hyperbolic
open Set

noncomputable def regularHexagonDiscHalfplaneInterior : Set ℂ :=
  {w | Complex.normSq w < 1 ∧ ∀ i : Fin 6, 0 < regularHexagonSideEquation i w}

theorem regular_hexagon_disc_halfplane_origin_mem :
    (0 : ℂ) ∈ regularHexagonDiscHalfplaneInterior := by
  constructor
  · norm_num
  · intro i; rw [regular_hexagon_side_equation_origin]; norm_num

theorem regular_hexagon_disc_halfplane_starConvex :
    StarConvex ℝ 0 regularHexagonDiscHalfplaneInterior := by
  intro w hw a b ha hb hab
  have hb₁ : b ≤ 1 := by linarith
  simp only [smul_zero, zero_add]
  change Complex.normSq ((b : ℂ) * w) < 1 ∧ ∀ i : Fin 6,
    0 < regularHexagonSideEquation i ((b : ℂ) * w)
  constructor
  · rw [Complex.normSq_mul, Complex.normSq_ofReal]
    have hb₂ : b ^ 2 ≤ 1 := by nlinarith
    calc b * b * Complex.normSq w ≤ 1 * Complex.normSq w :=
      mul_le_mul_of_nonneg_right (by nlinarith) (Complex.normSq_nonneg w)
      _ = Complex.normSq w := one_mul _
      _ < 1 := hw.1
  · intro i
    exact regular_hexagon_disc_side_radial_contraction i w b hw.1 hb hb₁ (hw.2 i)

theorem regular_hexagon_disc_halfplane_connected :
    IsConnected regularHexagonDiscHalfplaneInterior :=
  (regular_hexagon_disc_halfplane_starConvex.isPathConnected
    regular_hexagon_disc_halfplane_origin_mem).isConnected

end CurveComplex.Hyperbolic
