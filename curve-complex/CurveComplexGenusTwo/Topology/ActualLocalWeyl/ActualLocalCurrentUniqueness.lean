import CurveComplexGenusTwo.Topology.ActualLocalDbarSolvability.ActualLocalDbarContracts
import Mathlib.Analysis.Distribution.Distribution
import Mathlib.MeasureTheory.Measure.OpenPos

open scoped ContDiff Distributions
open TopologicalSpace MeasureTheory

namespace CanonicalDimensionTwo.LocalDbar

/-- The actual local integration current, with the approved 2i wedge
normalization. The formula theorem retains local integrability explicitly. -/
noncomputable def localCoefficientCurrent (Ω : Opens ℂ) (h : ℂ → ℂ) :
    TestFunction Ω ℂ ⊤ →L[ℂ] ℂ :=
  (2 * Complex.I) • TestFunction.integralAgainstBilinCLM
    (ContinuousLinearMap.lsmul ℂ ℂ) volume h

theorem localCoefficientCurrent_apply (Ω : Opens ℂ) (h : ℂ → ℂ)
    (hh : LocallyIntegrableOn h Ω volume) (φ : TestFunction Ω ℂ ⊤) :
    localCoefficientCurrent Ω h φ = ∫ z : ℂ, (2 * Complex.I) * φ z * h z := by
  rw [localCoefficientCurrent, ContinuousLinearMap.smul_apply,
    TestFunction.integralAgainstBilinCLM_eq_integral hh]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, mul_assoc,
    integral_const_mul]

/-- Smooth tests uniquely determine a continuous coefficient on the actual
open set, using Mathlib's distribution uniqueness and open-positive area. -/
theorem localCoefficientCurrent_injective_on_continuous
    (Ω : Opens ℂ) {h k : ℂ → ℂ} (hh : ContinuousOn h Ω) (hk : ContinuousOn k Ω)
    (he : localCoefficientCurrent Ω h = localCoefficientCurrent Ω k) :
    Set.EqOn h k Ω := by
  have hhI : LocallyIntegrableOn h Ω volume := hh.locallyIntegrableOn Ω.isOpen.measurableSet
  have hkI : LocallyIntegrableOn k Ω volume := hk.locallyIntegrableOn Ω.isOpen.measurableSet
  have hd : Distribution.ofFun Ω h volume ⊤ = Distribution.ofFun Ω k volume ⊤ := by
    ext φ
    let ψ : TestFunction Ω ℂ ⊤ := TestFunction.postcompCLM Complex.ofRealCLM φ
    have hφ := congrArg (fun T : TestFunction Ω ℂ ⊤ →L[ℂ] ℂ => T ψ) he
    rw [localCoefficientCurrent_apply Ω h hhI, localCoefficientCurrent_apply Ω k hkI] at hφ
    have hI : (2 * Complex.I : ℂ) ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
    have hcancel : (∫ z : ℂ, φ z • h z) = ∫ z : ℂ, φ z • k z := by
      apply mul_left_cancel₀ hI
      simpa [ψ, mul_assoc, integral_const_mul, Complex.real_smul] using hφ
    simpa only [Distribution.ofFun_apply hhI, Distribution.ofFun_apply hkI] using hcancel
  exact Measure.eqOn_open_of_ae_eq (Distribution.ofFun_injective hhI hkI hd)
    Ω.isOpen hh hk

end CanonicalDimensionTwo.LocalDbar
