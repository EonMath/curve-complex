import CurveComplexGenusTwo.Dictionary.JordanEssentiality

namespace CurveComplex.HyperellipticModel
open Set
noncomputable section

/-- Constructed inward radius, fixed at the common marked circle point. -/
def actualLoopParallelRadius (ρ : ℝ) (c : JordanPlane) (τ : Interval) (x : JordanPlane) : ℝ :=
  1-(1-ρ)*(τ.val*‖x-c‖^2)/8

theorem actual_loop_parallel_radius_bounds (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (c : JordanPlane) (hc : ‖c‖=1) (τ : Interval) (x : JordanPlane) (hx : ‖x‖=1) :
    ρ < actualLoopParallelRadius ρ c τ x ∧ actualLoopParallelRadius ρ c τ x ≤ 1 := by
  have hnorm : ‖x-c‖ ≤ 2 := by
    calc
      _ ≤ ‖x‖+‖c‖ := norm_sub_le x c
      _ = 2 := by rw [hx,hc]; norm_num
  have hsquare : ‖x-c‖^2 ≤ 4 := by nlinarith [norm_nonneg (x-c)]
  have hprod : 0 ≤ τ.val*‖x-c‖^2 := mul_nonneg τ.property.1 (sq_nonneg _)
  have hprod4 : τ.val*‖x-c‖^2 ≤ 4 :=
    (mul_le_mul_of_nonneg_right τ.property.2 (sq_nonneg _)).trans (by simpa using hsquare)
  have hscale := mul_le_mul_of_nonneg_left hprod4 (sub_nonneg.mpr hρ1.le)
  have hscale0 := mul_nonneg (sub_nonneg.mpr hρ1.le) hprod
  dsimp [actualLoopParallelRadius]
  constructor <;> nlinarith

theorem actual_loop_parallel_radius_strict (ρ : ℝ) (hρ1 : ρ < 1)
    (c : JordanPlane) (τ : Interval) (hτ : 0 < τ.val) (x : JordanPlane) (hx : x≠c) :
    actualLoopParallelRadius ρ c τ x < 1 := by
  have hn : 0 < ‖x-c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  have hh := mul_pos (sub_pos.mpr hρ1) (mul_pos hτ (sq_pos_of_pos hn))
  dsimp [actualLoopParallelRadius]
  linarith

/-- Actual inward parallel motion retains angular injectivity on the circle. -/
theorem actual_loop_parallel_unit_injective (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (c : JordanPlane) (hc : ‖c‖=1) (τ : Interval)
    (x y : JordanPlane) (hx : ‖x‖=1) (hy : ‖y‖=1)
    (he : actualLoopParallelRadius ρ c τ x • x = actualLoopParallelRadius ρ c τ y • y) : x=y := by
  have hrx := lt_trans hρ (actual_loop_parallel_radius_bounds ρ hρ hρ1 c hc τ x hx).1
  have hry := lt_trans hρ (actual_loop_parallel_radius_bounds ρ hρ hρ1 c hc τ y hy).1
  have hr : actualLoopParallelRadius ρ c τ x = actualLoopParallelRadius ρ c τ y := by
    have hh := congrArg norm he
    simpa [norm_smul,Real.norm_eq_abs,abs_of_pos hrx,abs_of_pos hry,hx,hy] using hh
  rw [← hr] at he
  have hh := congrArg (fun z : JordanPlane => (actualLoopParallelRadius ρ c τ x)⁻¹ • z) he
  simpa only [smul_smul,inv_mul_cancel₀ (ne_of_gt hrx),one_smul] using hh
end
end CurveComplex.HyperellipticModel
