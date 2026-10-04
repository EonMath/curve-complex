import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Basic

open Set Filter

theorem actual_open_sard_small_shift
    (f : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (r : ℝ) (hr : 0 < r) :
    ∃ c : ℂ, ‖c‖ < r ∧
      ∀ x ∈ U, f x + c = 0 → (fderiv ℝ f x).det ≠ 0 := by
  let C : Set ℂ := {x | x ∈ U ∧ (fderiv ℝ f x).det = 0}
  have hnull : MeasureTheory.volume (f '' C) = 0 := by
    apply MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
      (μ := MeasureTheory.volume) (f' := fun x => fderiv ℝ f x)
    · intro x hx
      exact (((hf x hx.1).contDiffAt (hU.mem_nhds hx.1)).differentiableAt
        (by norm_num)).hasFDerivAt.hasFDerivWithinAt
    · intro x hx
      exact hx.2
  have hball : 0 < MeasureTheory.volume (Metric.ball (0 : ℂ) r) :=
    Metric.measure_ball_pos MeasureTheory.volume 0 hr
  by_contra hnone
  have hsubset : Metric.ball (0 : ℂ) r ⊆ f '' C := by
    intro y hy
    by_contra hbad
    apply hnone
    refine ⟨-y, ?_, ?_⟩
    · simpa only [Metric.mem_ball, dist_zero_right, norm_neg] using hy
    · intro x hxU hx
      have hxy : f x = y := by simpa only [add_neg_eq_zero] using hx
      intro hdet
      exact hbad ⟨x, ⟨hxU, hdet⟩, hxy⟩
  exact (not_lt_of_ge ((MeasureTheory.measure_mono hsubset).trans_eq hnull)) hball

theorem actual_open_bumped_core_regularization
    (f : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U)
    (φ : ℂ → ℝ) (hφbound : ∀ z, φ z ≤ 1)
    (K : Set ℂ) (hKU : K ⊆ U)
    (hKφ : ∀ x ∈ K, φ x = 1)
    (hφdiff : ∀ x ∈ K, DifferentiableAt ℝ φ x)
    (r : ℝ) (hr : 0 < r) :
    ∃ c : ℂ, ‖c‖ < r ∧
      ∀ x ∈ K, f x + φ x • c = 0 →
        (fderiv ℝ (fun z => f z + φ z • c) x).det ≠ 0 := by
  obtain ⟨c, hc, hreg⟩ := actual_open_sard_small_shift f U hU hf r hr
  refine ⟨c, hc, ?_⟩
  intro x hx hzero
  have hfdiff : DifferentiableAt ℝ f x :=
    ((hf x (hKU hx)).contDiffAt (hU.mem_nhds (hKU hx))).differentiableAt
      (by norm_num)
  have hmax : IsLocalMax φ x :=
    Filter.Eventually.of_forall (fun z => by simpa only [hKφ x hx] using hφbound z)
  have hφzero : fderiv ℝ φ x = 0 := hmax.fderiv_eq_zero
  have hval : f x + φ x • c = f x + c := by simp [hKφ x hx]
  have hderiv : fderiv ℝ (fun z => f z + φ z • c) x = fderiv ℝ f x := by
    change fderiv ℝ (f + fun z => φ z • c) x = _
    rw [fderiv_add hfdiff ((hφdiff x hx).smul_const c)]
    rw [fderiv_smul_const (hφdiff x hx) c, hφzero]
    simp
  rw [hderiv]
  exact hreg x (hKU hx) (hval.symm.trans hzero)

#print axioms actual_open_bumped_core_regularization
