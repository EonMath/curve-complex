import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Complex.Basic

open InnerProductSpace

theorem actual_complex_real_basis_decomposition (c : ℂ) :
    c.re • (1 : ℂ) + c.im • Complex.I = c := by
  apply Complex.ext
  · simp
  · simp

theorem actual_real_dual_complex_basis_decomposition (c z : ℂ) :
    (toDual ℝ ℂ c) z =
      c.re * (toDual ℝ ℂ (1 : ℂ)) z +
      c.im * (toDual ℝ ℂ Complex.I) z := by
  conv_lhs => rw [← actual_complex_real_basis_decomposition c]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]


theorem actual_bumped_chart_dual_parameter_decomposition
    (b : ℝ) (c z : ℂ) :
    b * (toDual ℝ ℂ c) z =
      c.re * (b * (toDual ℝ ℂ (1 : ℂ)) z) +
      c.im * (b * (toDual ℝ ℂ Complex.I) z) := by
  rw [actual_real_dual_complex_basis_decomposition]
  ring

