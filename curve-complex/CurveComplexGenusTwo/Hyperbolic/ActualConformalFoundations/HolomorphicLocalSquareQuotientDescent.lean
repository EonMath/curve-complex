import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

set_option backward.isDefEq.respectTransparency false
open Filter Topology

theorem holomorphic_local_square_quotient_descent (F : ℂ → ℂ) (s : Set ℂ) (hs : IsOpen s)
    (hc : ContinuousOn F s)
    (hpull : DifferentiableOn ℂ (fun z : ℂ => F (z ^ 2))
      ((fun z : ℂ => z ^ 2) ⁻¹' s)) : DifferentiableOn ℂ F s := by
  have hregular : ∀ w : ℂ, w ∈ s → w ≠ 0 → DifferentiableAt ℂ F w := by
    intro w hws hw
    obtain ⟨z, hz⟩ := (Complex.isOpenQuotientMap_pow 2).surjective w
    have hz0 : z ≠ 0 := by
      intro h
      apply hw
      simpa [h] using hz.symm
    have hd : HasStrictDerivAt (fun z : ℂ => z ^ 2) (2 * z) z := by
      simpa using (hasStrictDerivAt_id z).fun_pow 2
    have hdn : (2 : ℂ) * z ≠ 0 := mul_ne_zero (by norm_num) hz0
    let inv := hd.localInverse (fun z : ℂ => z ^ 2) (2 * z) z hdn
    have hinv : HasStrictDerivAt inv (2 * z)⁻¹ w := by
      rw [← hz]
      exact hd.to_localInverse hdn
    have hright : ∀ᶠ v in 𝓝 w, (inv v) ^ 2 = v := by
      rw [← hz]
      exact hd.eventually_right_inverse hdn
    have hcomp : DifferentiableAt ℂ (fun v => F ((inv v) ^ 2)) w :=
      (hpull.differentiableAt ((hs.preimage
        (Complex.isOpenQuotientMap_pow 2).continuous).mem_nhds (by
          change (inv w) ^ 2 ∈ s
          rw [hright.self_of_nhds]
          exact hws))).comp w hinv.hasDerivAt.differentiableAt
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [hright] with v hv
    rw [hv]
  have hzero : 0 ∈ s → DifferentiableAt ℂ F 0 := by
    intro hz
    apply (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      ?_ (hc.continuousAt (hs.mem_nhds hz))).differentiableAt
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ s from hs.mem_nhds hz).filter_mono nhdsWithin_le_nhds] with z hzn hzs
    exact hregular z hzs hzn
  intro w hws
  by_cases hw : w = 0
  · subst w
    exact (hzero hws).differentiableWithinAt
  · exact (hregular w hws hw).differentiableWithinAt
