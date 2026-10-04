import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Complex.Basic

open Set Filter Topology

theorem actual_plateau_affine_fderiv_shift
    (f b : ℂ → ℝ) (L : ℂ →L[ℝ] ℝ) (c : ℝ)
    (U : Set ℂ) (hU : IsOpen U) (hb : ∀ z ∈ U, b z = 1)
    (x : ℂ) (hx : x ∈ U) (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun z => f z + c * (b z * L z)) x =
      fderiv ℝ f x + c • L := by
  have heq : (fun z => f z + c * (b z * L z)) =ᶠ[𝓝 x]
      (fun z => f z + c * L z) := by
    filter_upwards [hU.mem_nhds hx] with z hz
    simp [hb z hz]
  rw [Filter.EventuallyEq.fderiv_eq heq]
  have hderiv : HasFDerivAt (fun z => f z + c * L z)
      (fderiv ℝ f x + c • L) x := by
    convert hf.hasFDerivAt.add (L.hasFDerivAt.const_smul c) using 1
  exact hderiv.fderiv

