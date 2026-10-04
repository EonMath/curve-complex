import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Complex.Basic

private theorem actual_zero_clm_apply_derivative
    (A : ℂ → ℂ →L[ℝ] ℂ) (g : ℂ → ℂ)
    (hA : DifferentiableAt ℝ A 0)
    (D : ℂ →L[ℝ] ℂ) (hg : HasFDerivAt g D 0) (hg0 : g 0 = 0) :
    HasFDerivAt (fun w => A w (g w)) ((A 0).comp D) 0 := by
  have h := hA.hasFDerivAt.clm_apply hg
  have hflip : (fderiv ℝ A 0).flip (g 0) = 0 := by
    rw [hg0]
    ext w
    simp
  rw [hflip, add_zero] at h
  exact h

theorem actual_zero_derivative_transport_rule
    (A : ℂ → ℂ →L[ℝ] ℂ) (g h : ℂ → ℂ)
    (hA : DifferentiableAt ℝ A 0)
    (L D H : ℂ ≃L[ℝ] ℂ)
    (hL : A 0 = L.toContinuousLinearMap)
    (hg : HasFDerivAt g D.toContinuousLinearMap 0) (hg0 : g 0 = 0)
    (hh : HasFDerivAt h H.toContinuousLinearMap 0) (hh0 : h 0 = 0) :
    ∃ T : ℂ ≃L[ℝ] ℂ,
      HasFDerivAt (fun w => A w (g (h w))) T.toContinuousLinearMap 0 := by
  let T : ℂ ≃L[ℝ] ℂ := H.trans (D.trans L)
  have hcomp : HasFDerivAt (g ∘ h)
      (D.toContinuousLinearMap.comp H.toContinuousLinearMap) 0 := by
    have hg' : HasFDerivAt g D.toContinuousLinearMap (h 0) := by
      simpa only [hh0] using hg
    exact hg'.comp 0 hh
  have hcomp0 : (g ∘ h) 0 = 0 := by simp [hh0, hg0]
  have h := actual_zero_clm_apply_derivative A (g ∘ h) hA
    (D.toContinuousLinearMap.comp H.toContinuousLinearMap) hcomp hcomp0
  refine ⟨T, ?_⟩
  convert h using 1
  · ext w
    rfl
  · ext w
    simp [T, hL]

#print axioms actual_zero_derivative_transport_rule
