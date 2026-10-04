import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Complex.Basic

open Filter Topology

theorem holomorphic_involution_branch_coordinate (f : ℂ → ℂ) (a : ℂ) (hfix : f a = a)
    (hinv : ∀ᶠ z in 𝓝 a, f (f z) = z)
    (hderiv : HasStrictDerivAt f (-1) a) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      a ∈ e.source ∧ e a = 0 ∧
      HasStrictDerivAt (fun z => e z) 1 a ∧
      (∀ᶠ z in 𝓝 a, e (f z) = -e z) ∧
      (∀ᶠ z in 𝓝 a, (e (f z)) ^ 2 = (e z) ^ 2) := by
  let ψ : ℂ → ℂ := fun z => (z - f z) / 2
  have hd : HasStrictDerivAt ψ 1 a := by
    convert (hasStrictDerivAt_id a).sub hderiv |>.div_const (2 : ℂ) using 1 <;>
      norm_num [ψ]
  let hd' := hd.hasStrictFDerivAt_equiv (by norm_num : (1 : ℂ) ≠ 0)
  let e := hd'.toOpenPartialHomeomorph ψ
  have he : (e : ℂ → ℂ) = ψ := hd'.toOpenPartialHomeomorph_coe
  have hneg : ∀ᶠ z in 𝓝 a, e (f z) = -e z := by
    filter_upwards [hinv] with z hz
    rw [he]
    dsimp [ψ]
    rw [hz]
    ring
  refine ⟨e, hd'.mem_toOpenPartialHomeomorph_source, ?_, ?_, hneg, ?_⟩
  · rw [he]
    simp [ψ, hfix]
  · rw [he]
    exact hd
  · filter_upwards [hneg] with z hz
    rw [hz]
    ring
