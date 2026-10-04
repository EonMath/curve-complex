import CurveComplexGenusTwo.Hyperbolic.ActualConformalFoundations.HolomorphicInvolutionBranchCoordinate
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

open Filter Topology

theorem holomorphic_involution_biholomorphic_branch_coordinate (f : ℂ → ℂ) (a : ℂ) (hfix : f a = a)
    (hinv : ∀ᶠ z in 𝓝 a, f (f z) = z)
    (hderiv : HasStrictDerivAt f (-1) a)
    (hhol : ContDiffAt ℂ 1 f a) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      a ∈ e.source ∧ e a = 0 ∧
      (∀ᶠ z in 𝓝 a, ContDiffAt ℂ 1 (fun z => e z) z) ∧
      (∀ᶠ w in 𝓝 (0 : ℂ), ContDiffAt ℂ 1 (fun w => e.symm w) w) ∧
      (∀ᶠ z in 𝓝 a, e (f z) = -e z) ∧
      (∀ᶠ z in 𝓝 a, (e (f z)) ^ 2 = (e z) ^ 2) := by
  let ψ : ℂ → ℂ := fun z => (z - f z) / 2
  have hd : HasStrictDerivAt ψ 1 a := by
    convert (hasStrictDerivAt_id a).sub hderiv |>.div_const (2 : ℂ) using 1 <;>
      norm_num [ψ]
  have hc : ContDiffAt ℂ 1 ψ a :=
    (contDiffAt_id.sub hhol).div_const (2 : ℂ)
  let hd' := hd.hasStrictFDerivAt_equiv (by norm_num : (1 : ℂ) ≠ 0)
  let e := hd'.toOpenPartialHomeomorph ψ
  have he : (e : ℂ → ℂ) = ψ := hd'.toOpenPartialHomeomorph_coe
  have hzero : e a = 0 := by rw [he]; simp [ψ, hfix]
  have hcinv : ContDiffAt ℂ 1 (fun w => e.symm w) 0 := by
    rw [← hzero]
    apply e.contDiffAt_symm (e.map_source hd'.mem_toOpenPartialHomeomorph_source)
    · rw [e.left_inv hd'.mem_toOpenPartialHomeomorph_source, he]
      exact hd'.hasFDerivAt
    · rw [e.left_inv hd'.mem_toOpenPartialHomeomorph_source, he]
      exact hc
  have hneg : ∀ᶠ z in 𝓝 a, e (f z) = -e z := by
    filter_upwards [hinv] with z hz
    rw [he]
    dsimp [ψ]
    rw [hz]
    ring
  refine ⟨e, hd'.mem_toOpenPartialHomeomorph_source, hzero, ?_,
    hcinv.eventually (by norm_num), hneg, ?_⟩
  · rw [he]
    exact hc.eventually (by norm_num)
  · filter_upwards [hneg] with z hz
    rw [hz]
    ring
