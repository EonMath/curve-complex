import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Algebra.Module.Equiv.Basic
import Mathlib.Analysis.Complex.Basic

open Filter
open scoped Topology

theorem actual_local_inverse_derivative_equiv
    (h k : ℂ → ℂ)
    (hh : ContDiffAt ℝ 1 h 0) (hk : ContDiffAt ℝ 1 k 0)
    (hh0 : h 0 = 0) (hk0 : k 0 = 0)
    (hkh : (fun w => k (h w)) =ᶠ[𝓝 (0 : ℂ)] id)
    (hhk : (fun w => h (k w)) =ᶠ[𝓝 (0 : ℂ)] id) :
    ∃ H : ℂ ≃L[ℝ] ℂ,
      HasFDerivAt h H.toContinuousLinearMap 0 := by
  let dh := fderiv ℝ h 0
  let dk := fderiv ℝ k 0
  have hdh : HasFDerivAt h dh 0 :=
    (hh.differentiableAt (by norm_num)).hasFDerivAt
  have hdk : HasFDerivAt k dk 0 :=
    (hk.differentiableAt (by norm_num)).hasFDerivAt
  have hkh' : dk.comp dh = ContinuousLinearMap.id ℝ ℂ := by
    have hdk' : HasFDerivAt k dk (h 0) := by simpa only [hh0] using hdk
    have hcomp := hdk'.comp 0 hdh
    have hid : fderiv ℝ (fun w => k (h w)) 0 = ContinuousLinearMap.id ℝ ℂ := by
      rw [hkh.fderiv_eq]
      exact fderiv_id
    exact hcomp.fderiv.symm.trans hid
  have hhk' : dh.comp dk = ContinuousLinearMap.id ℝ ℂ := by
    have hdh' : HasFDerivAt h dh (k 0) := by simpa only [hk0] using hdh
    have hcomp := hdh'.comp 0 hdk
    have hid : fderiv ℝ (fun w => h (k w)) 0 = ContinuousLinearMap.id ℝ ℂ := by
      rw [hhk.fderiv_eq]
      exact fderiv_id
    exact hcomp.fderiv.symm.trans hid
  let H := ContinuousLinearEquiv.equivOfInverse' dh dk hhk' hkh'
  exact ⟨H, hdh⟩

#print axioms actual_local_inverse_derivative_equiv
