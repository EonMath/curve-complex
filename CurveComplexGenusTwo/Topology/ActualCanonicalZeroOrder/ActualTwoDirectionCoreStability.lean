import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualTwoDirectionCoreStability
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.Basic

open Set

theorem actual_two_direction_compact_regular_small_shifts
    (f g h : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (hg : ContDiffOn ℝ 1 g U)
    (hh : ContDiffOn ℝ 1 h U)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U)
    (hzero : ∀ x ∈ K, f x = 0 → (fderiv ℝ f x).det ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ c : ℂ, ‖c‖ < r →
      ∀ x ∈ K, f x + c.re • g x + c.im • h x = 0 →
        (fderiv ℝ (fun z => f z + c.re • g z + c.im • h z) x).det ≠ 0 := by
  let P : Set (ℝ × ℝ) := {p | ∀ x ∈ K,
    f x + p.1 • g x + p.2 • h x = 0 →
      (fderiv ℝ (fun z => f z + p.1 • g z + p.2 • h z) x).det ≠ 0}
  have hP : IsOpen P :=
    actual_two_direction_compact_regular_parameters f g h U hU hf hg hh K hK hKU
  have h00 : ((0 : ℝ), (0 : ℝ)) ∈ P := by
    intro x hx hfx
    have hfx0 : f x = 0 := by simpa using hfx
    simpa only [zero_smul, add_zero] using hzero x hx hfx0
  let Q : Set ℂ := {c | (c.re, c.im) ∈ P}
  have hQ : IsOpen Q := hP.preimage (Complex.continuous_re.prodMk Complex.continuous_im)
  have hQ0 : (0 : ℂ) ∈ Q := by
    change ((0 : ℝ), (0 : ℝ)) ∈ P
    exact h00
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hQ 0 hQ0
  refine ⟨r, hr, fun c hc => ?_⟩
  exact hball (by simpa only [Metric.mem_ball, dist_zero_right] using hc)

#print axioms actual_two_direction_compact_regular_small_shifts
