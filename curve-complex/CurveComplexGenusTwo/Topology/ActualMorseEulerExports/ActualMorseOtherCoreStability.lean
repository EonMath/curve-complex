import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualMorseAffineCoordinateBasis
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualMorseCoreParameterStability
import CurveComplexGenusTwo.Topology.ActualSmoothMorseNormalForm.ActualMorseChartPullbackSmooth

open scoped Manifold ContDiff
open Set InnerProductSpace

theorem actual_morse_other_core_parameter_stability
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (pi pj : E) (F b : E → ℝ)
    (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F)
    (hb : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ b)
    (hs : tsupport b ⊆ (chartAt ℂ pi).source)
    (Kj : Set E) (hKj : IsCompact Kj)
    (hKsource : Kj ⊆ (chartAt ℂ pj).source) :
    let Kc : Set ℂ := (chartAt ℂ pj) '' Kj;
    IsOpen {c : ℂ | ∀ z ∈ Kc,
      gradient (fun w =>
        let x := (chartAt ℂ pj).symm w
        F x + b x * (toDual ℝ ℂ c) ((chartAt ℂ pi) x)) z = 0 →
      (fderiv ℝ (gradient (fun w =>
        let x := (chartAt ℂ pj).symm w
        F x + b x * (toDual ℝ ℂ c) ((chartAt ℂ pi) x))) z).det ≠ 0} := by
  let ci := chartAt ℂ pi
  let cj := chartAt ℂ pj
  let G : E → ℝ := fun x => b x * (toDual ℝ ℂ (1 : ℂ)) (ci x)
  let H : E → ℝ := fun x => b x * (toDual ℝ ℂ Complex.I) (ci x)
  let Kc : Set ℂ := cj '' Kj
  have hG : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ G :=
    actual_chart_linear_bump_smooth pi b (toDual ℝ ℂ (1 : ℂ)) hb hs
  have hH : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ H :=
    actual_chart_linear_bump_smooth pi b (toDual ℝ ℂ Complex.I) hb hs
  have hKc : IsCompact Kc :=
    hKj.image_of_continuousOn (cj.continuousOn.mono hKsource)
  have hKtarget : Kc ⊆ cj.target := by
    rintro z ⟨x, hx, rfl⟩
    exact cj.map_source (hKsource hx)
  have hopen := actual_morse_compact_core_scalar_parameters_open
    (fun w => F (cj.symm w)) (fun w => G (cj.symm w))
    (fun w => H (cj.symm w)) cj.target cj.open_target
    (actual_smooth_scalar_chart_pullback_contDiffOn pj F hF)
    (actual_smooth_scalar_chart_pullback_contDiffOn pj G hG)
    (actual_smooth_scalar_chart_pullback_contDiffOn pj H hH)
    Kc hKc hKtarget
  have hmap : Continuous (fun c : ℂ => (c.re, c.im)) :=
    Complex.continuous_re.prodMk Complex.continuous_im
  have hpre := hopen.preimage hmap
  convert hpre using 1
  ext c
  have heq : (fun w : ℂ =>
      let x := cj.symm w
      F x + b x * (toDual ℝ ℂ c) (ci x)) =
      (fun w => F (cj.symm w) + c.re * G (cj.symm w) +
        c.im * H (cj.symm w)) := by
    funext w
    change F (cj.symm w) + b (cj.symm w) * (toDual ℝ ℂ c) (ci (cj.symm w)) =
      F (cj.symm w) +
        c.re * (b (cj.symm w) * (toDual ℝ ℂ (1 : ℂ)) (ci (cj.symm w))) +
        c.im * (b (cj.symm w) * (toDual ℝ ℂ Complex.I) (ci (cj.symm w)))
    rw [actual_bumped_chart_dual_parameter_decomposition]
    ring
  change (∀ z ∈ Kc,
      gradient (fun w =>
        let x := cj.symm w
        F x + b x * (toDual ℝ ℂ c) (ci x)) z = 0 →
      (fderiv ℝ (gradient (fun w =>
        let x := cj.symm w
        F x + b x * (toDual ℝ ℂ c) (ci x))) z).det ≠ 0) ↔
    ∀ z ∈ Kc,
      gradient (fun w => F (cj.symm w) + c.re * G (cj.symm w) +
        c.im * H (cj.symm w)) z = 0 →
      (fderiv ℝ (gradient (fun w => F (cj.symm w) + c.re * G (cj.symm w) +
        c.im * H (cj.symm w))) z).det ≠ 0
  rw [heq]

