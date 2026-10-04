import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualMorseGradientShift
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualTwoDirectionCoreStability

open Set InnerProductSpace

theorem actual_gradient_contDiffOn_of_scalar_contDiffOn
    (f : ℂ → ℝ) (U : Set ℂ) (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) :
    ContDiffOn ℝ 1 (gradient f) U := by
  have hfder : ContDiffOn ℝ 1 (fderiv ℝ f) U :=
    hf.fderiv_of_isOpen hU (by norm_num)
  change ContDiffOn ℝ 1
    (fun x => (toDual ℝ ℂ).symm (fderiv ℝ f x)) U
  exact ((toDual ℝ ℂ).symm.toContinuousLinearMap.contDiff.contDiffOn
    (s := Set.univ)).comp hfder (by simp)


theorem actual_gradient_affine_scalar_combination
    (f g h : ℂ → ℝ) (a b : ℝ) (x : ℂ)
    (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x)
    (hh : DifferentiableAt ℝ h x) :
    gradient (fun z => f z + a * g z + b * h z) x =
      gradient f x + a • gradient g x + b • gradient h x := by
  have hderiv : fderiv ℝ (fun z => f z + a * g z + b * h z) x =
      fderiv ℝ f x + a • fderiv ℝ g x + b • fderiv ℝ h x := by
    change fderiv ℝ (f + a • g + b • h) x = _
    rw [fderiv_add (hf.add (hg.const_smul a)) (hh.const_smul b)]
    rw [fderiv_add hf (hg.const_smul a)]
    rw [fderiv_const_smul hg a, fderiv_const_smul hh b]
  simp only [gradient, hderiv, map_add, map_smul]


theorem actual_morse_compact_core_gradient_parameters_open
    (f g h : ℂ → ℝ) (U : Set ℂ) (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) (hg : ContDiffOn ℝ 2 g U)
    (hh : ContDiffOn ℝ 2 h U)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U) :
    IsOpen {p : ℝ × ℝ | ∀ x ∈ K,
      gradient f x + p.1 • gradient g x + p.2 • gradient h x = 0 →
        (fderiv ℝ (fun z =>
          gradient f z + p.1 • gradient g z + p.2 • gradient h z) x).det ≠ 0} := by
  exact actual_two_direction_compact_regular_parameters
    (gradient f) (gradient g) (gradient h) U hU
    (actual_gradient_contDiffOn_of_scalar_contDiffOn f U hU hf)
    (actual_gradient_contDiffOn_of_scalar_contDiffOn g U hU hg)
    (actual_gradient_contDiffOn_of_scalar_contDiffOn h U hU hh)
    K hK hKU


theorem actual_morse_compact_core_scalar_parameters_open
    (f g h : ℂ → ℝ) (U : Set ℂ) (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) (hg : ContDiffOn ℝ 2 g U)
    (hh : ContDiffOn ℝ 2 h U)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U) :
    IsOpen {p : ℝ × ℝ | ∀ x ∈ K,
      gradient (fun z => f z + p.1 * g z + p.2 * h z) x = 0 →
        (fderiv ℝ (gradient (fun z => f z + p.1 * g z + p.2 * h z)) x).det ≠ 0} := by
  have hopen := actual_morse_compact_core_gradient_parameters_open
    f g h U hU hf hg hh K hK hKU
  have heq (p : ℝ × ℝ) (z : ℂ) (hz : z ∈ U) :
      gradient (fun w => f w + p.1 * g w + p.2 * h w) z =
        gradient f z + p.1 • gradient g z + p.2 • gradient h z := by
    have hdiff (v : ℂ → ℝ) (hv : ContDiffOn ℝ 2 v U) :
        DifferentiableAt ℝ v z :=
      ((hv z hz).contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num)
    exact actual_gradient_affine_scalar_combination f g h p.1 p.2 z
      (hdiff f hf) (hdiff g hg) (hdiff h hh)
  have hderiv (p : ℝ × ℝ) (x : ℂ) (hx : x ∈ U) :
      fderiv ℝ (gradient (fun z => f z + p.1 * g z + p.2 * h z)) x =
        fderiv ℝ (fun z => gradient f z + p.1 • gradient g z +
          p.2 • gradient h z) x := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hU.mem_nhds hx] with z hz
    exact heq p z hz
  convert hopen using 1
  ext p
  simp only [Set.mem_ofPred_eq]
  constructor <;> intro hp x hx hz
  · rw [← hderiv p x (hKU hx)]
    exact hp x hx ((heq p x (hKU hx)).trans hz)
  · rw [hderiv p x (hKU hx)]
    exact hp x hx ((heq p x (hKU hx)).symm.trans hz)

