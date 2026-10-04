import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Perfect
import Mathlib.Analysis.Complex.Basic

open Filter Topology

theorem isolated_involution_strict_derivative_negative (f : ℂ → ℂ) (a d : ℂ) (hfix : f a = a)
    (hinv : ∀ᶠ z in 𝓝 a, f (f z) = z)
    (hisolated : ∀ᶠ z in 𝓝[≠] a, f z ≠ z)
    (hd : HasStrictDerivAt f d a) : d = -1 := by
  have hdisj : d = 1 ∨ d = -1 := by
    have hd' : HasStrictDerivAt f d (f a) := hfix.symm ▸ hd
    have hcomp : HasStrictDerivAt (fun z => f (f z)) (d * d) a := hd'.comp a hd
    have hid : HasStrictDerivAt (fun z : ℂ => z) (d * d) a :=
      hcomp.congr_of_eventuallyEq hinv
    have heq : d * d = 1 := hid.hasDerivAt.unique (hasDerivAt_id a)
    have hprod : (d - 1) * (d + 1) = 0 := by linear_combination heq
    rcases mul_eq_zero.mp hprod with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  rcases hdisj with hone | hminus
  · exfalso
    subst d
    let ψ : ℂ → ℂ := fun z => (z + f z) / 2
    have hψ : HasStrictDerivAt ψ 1 a := by
      convert (hasStrictDerivAt_id a).add hd |>.div_const (2 : ℂ) using 1 <;>
        norm_num [ψ]
    let inverse := hψ.localInverse ψ 1 a (by norm_num)
    have hleft : ∀ᶠ z in 𝓝 a, inverse (ψ z) = z :=
      hψ.eventually_left_inverse (by norm_num)
    have ht : Tendsto f (𝓝 a) (𝓝 a) := by
      simpa [hfix] using hd.hasDerivAt.continuousAt.tendsto
    have heq : ∀ᶠ z in 𝓝 a, f z = z := by
      filter_upwards [hinv, hleft, ht.eventually hleft] with z hz hzl hzfl
      have hinvariant : ψ (f z) = ψ z := by dsimp [ψ]; rw [hz]; ring
      rw [hinvariant, hzl] at hzfl
      exact hzfl.symm
    have heq' : ∀ᶠ z in 𝓝[≠] a, f z = z := heq.filter_mono nhdsWithin_le_nhds
    obtain ⟨z, hz, hn⟩ := (heq'.and hisolated).exists
    exact hn hz
  · exact hminus
