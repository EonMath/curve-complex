import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualMorsePlateauDerivative
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Comp
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualMorseSardCore

open Set InnerProductSpace Filter Topology

theorem actual_plateau_gradient_shift
    (f b : ℂ → ℝ) (c : ℂ)
    (U : Set ℂ) (hU : IsOpen U) (hb : ∀ z ∈ U, b z = 1)
    (x : ℂ) (hx : x ∈ U) (hf : DifferentiableAt ℝ f x) :
    gradient (fun z => f z + b z * (toDual ℝ ℂ c) z) x =
      gradient f x + c := by
  have hderiv := actual_plateau_affine_fderiv_shift f b (toDual ℝ ℂ c) 1
    U hU hb x hx hf
  simp only [one_mul, one_smul] at hderiv
  simp only [gradient, hderiv, map_add, (toDual ℝ ℂ).symm_apply_apply]


theorem actual_morse_small_shift_regular_on_plateau
    (f b : ℂ → ℝ) (U : Set ℂ) (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) (hb : ∀ z ∈ U, b z = 1)
    (r : ℝ) (hr : 0 < r) :
    ∃ c : ℂ, ‖c‖ < r ∧
      ∀ x ∈ U,
        gradient (fun z => f z + b z * (toDual ℝ ℂ c) z) x = 0 →
        (fderiv ℝ (gradient f) x).det ≠ 0 := by
  have hfder : ContDiffOn ℝ 1 (fderiv ℝ f) U :=
    hf.fderiv_of_isOpen hU (by norm_num)
  have hgrad : ContDiffOn ℝ 1 (gradient f) U := by
    change ContDiffOn ℝ 1
      (fun x => (toDual ℝ ℂ).symm (fderiv ℝ f x)) U
    exact ((toDual ℝ ℂ).symm.toContinuousLinearMap.contDiff.contDiffOn
      (s := Set.univ)).comp hfder (by simp)
  obtain ⟨c, hc, hregular⟩ :=
    actual_morse_sard_small_gradient_shift (gradient f) U hU hgrad r hr
  refine ⟨c, hc, ?_⟩
  intro x hx hcritical
  have hdiff : DifferentiableAt ℝ f x :=
    ((hf x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  rw [actual_plateau_gradient_shift f b c U hU hb x hx hdiff] at hcritical
  exact hregular x hx hcritical


theorem actual_morse_small_shift_nondegenerate_on_plateau
    (f b : ℂ → ℝ) (U : Set ℂ) (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) (hb : ∀ z ∈ U, b z = 1)
    (r : ℝ) (hr : 0 < r) :
    ∃ c : ℂ, ‖c‖ < r ∧
      ∀ x ∈ U,
        gradient (fun z => f z + b z * (toDual ℝ ℂ c) z) x = 0 →
        (fderiv ℝ (gradient
          (fun z => f z + b z * (toDual ℝ ℂ c) z)) x).det ≠ 0 := by
  obtain ⟨c, hc, hregular⟩ :=
    actual_morse_small_shift_regular_on_plateau f b U hU hf hb r hr
  refine ⟨c, hc, ?_⟩
  intro x hx hzero
  have hgrad : (gradient (fun z => f z + b z * (toDual ℝ ℂ c) z)) =ᶠ[𝓝 x]
      (fun z => gradient f z + c) := by
    filter_upwards [hU.mem_nhds hx] with z hz
    have hdiff : DifferentiableAt ℝ f z :=
      ((hf z hz).contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num)
    exact actual_plateau_gradient_shift f b c U hU hb z hz hdiff
  rw [Filter.EventuallyEq.fderiv_eq hgrad, fderiv_add_const]
  exact hregular x hx hzero

