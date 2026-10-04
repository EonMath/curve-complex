import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualMorseGlobalGradientField
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Set

theorem actual_finite_weighted_gradient_energy_positive
    {ι : Type*} [Fintype ι] (b : ι → ℝ) (g : ι → ℂ)
    (hb : ∀ i, 0 ≤ b i)
    (i : ι) (hi : b i = 1) (hgi : g i ≠ 0) :
    0 < ∑ j, b j * ‖g j‖ ^ 2 := by
  have hterm (j : ι) : 0 ≤ b j * ‖g j‖ ^ 2 :=
    mul_nonneg (hb j) (sq_nonneg _)
  have hpositive : 0 < b i * ‖g i‖ ^ 2 := by
    rw [hi, one_mul]
    exact sq_pos_of_pos (norm_pos_iff.mpr hgi)
  exact hpositive.trans_le
    (Finset.single_le_sum (fun j hj => hterm j) (Finset.mem_univ i))

