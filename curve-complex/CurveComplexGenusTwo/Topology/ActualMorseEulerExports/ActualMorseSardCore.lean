import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Basic

open Set

theorem actual_morse_sard_small_gradient_shift
    (g : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hg : ContDiffOn ℝ 1 g U)
    (r : ℝ) (hr : 0 < r) :
    ∃ c : ℂ, ‖c‖ < r ∧
      ∀ x ∈ U, g x + c = 0 → (fderiv ℝ g x).det ≠ 0 := by
  let C : Set ℂ := {x | x ∈ U ∧ (fderiv ℝ g x).det = 0}
  have hnull : MeasureTheory.volume (g '' C) = 0 := by
    apply MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
      (μ := MeasureTheory.volume) (f' := fun x => fderiv ℝ g x)
    · intro x hx
      exact (((hg x hx.1).contDiffAt (hU.mem_nhds hx.1)).differentiableAt
        (by norm_num)).hasFDerivAt.hasFDerivWithinAt
    · intro x hx
      exact hx.2
  have hball : 0 < MeasureTheory.volume (Metric.ball (0 : ℂ) r) :=
    Metric.measure_ball_pos MeasureTheory.volume 0 hr
  by_contra hnone
  have hsubset : Metric.ball (0 : ℂ) r ⊆ g '' C := by
    intro y hy
    by_contra hbad
    apply hnone
    refine ⟨-y, ?_, ?_⟩
    · simpa only [Metric.mem_ball, dist_zero_right, norm_neg] using hy
    · intro x hxU hx
      have hxy : g x = y := by simpa only [add_neg_eq_zero] using hx
      intro hdet
      exact hbad ⟨x, ⟨hxU, hdet⟩, hxy⟩
  exact (not_lt_of_ge ((MeasureTheory.measure_mono hsubset).trans_eq hnull)) hball

