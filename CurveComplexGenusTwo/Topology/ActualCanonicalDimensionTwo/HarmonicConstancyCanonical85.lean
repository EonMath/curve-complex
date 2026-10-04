import CurveComplexGenusTwo.Topology.ActualCanonicalDimensionTwo.ActualMixedPrimitiveCanonical85
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Topology.Connected.Clopen

open scoped Manifold ContDiff Bundle Topology
open InnerProductSpace
open Filter Set

namespace CanonicalDimensionTwo

private theorem harmonic_local_max_eq {g : ℂ → ℝ} {z : ℂ}
    (hg : HarmonicAt g z) (hm : IsLocalMax g z) :
    ∀ᶠ w in 𝓝 z, g w = g z := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_setOfPred_harmonicAt g).mem_nhds hg)
  have hH : HarmonicOnNhd g (Metric.ball z r) := fun w hw => hball hw
  obtain ⟨F, hFa, hFre⟩ := HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq hH
  have hz : z ∈ Metric.ball z r := Metric.mem_ball_self hr
  have hmax : IsLocalMax (fun w => ‖Complex.exp (F w)‖) z := by
    have h := hm.comp_mono Real.exp_monotone
    apply h.congr
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
    simp only [Complex.norm_exp]
    exact congrArg Real.exp (hFre hw).symm
  have hd : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (fun w => Complex.exp (F w)) w := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
    exact Complex.differentiableAt_exp.comp w (hFa w hw).differentiableAt
  filter_upwards [Complex.eventually_eq_of_isLocalMax_norm hd hmax,
    Metric.isOpen_ball.mem_nhds hz] with w he hw
  apply Real.exp_injective
  have he' := congrArg norm he
  simpa [Complex.norm_exp, hFre hw, hFre hz] using he'

private theorem compact_chartwise_real_harmonic_eq
    (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ∞ E] [CompactSpace E] [PreconnectedSpace E]
    (g : E → ℝ)
    (hg : ∀ q : E,
      HarmonicAt (fun w : ℂ => g ((chartAt ℂ q).symm w))
        ((chartAt ℂ q) q))
    (x y : E) : g x = g y := by
  have hcont : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro q
    let c := chartAt ℂ q
    have hq : q ∈ c.source := mem_chart_source ℂ q
    have hcx : c q ∈ c.target := c.map_source hq
    have hlocal : ContinuousAt (fun w : ℂ => g (c.symm w)) (c q) :=
      (hg q).1.continuousAt
    have hcomp := hlocal.comp (c.continuousAt hq)
    have hlocalEq : (fun q' => g (c.symm (c q'))) =ᶠ[𝓝 q] g := by
      filter_upwards [c.open_source.mem_nhds hq] with q' hq'
      simp [c.left_inv hq']
    exact hcomp.congr_of_eventuallyEq hlocalEq.symm
  obtain ⟨p, -, hp⟩ := isCompact_univ.exists_isMaxOn ⟨x, Set.mem_univ x⟩
    hcont.continuousOn
  have hp : ∀ q : E, g q ≤ g p := fun q => hp (Set.mem_univ q)
  let S : Set E := {q | g q = g p}
  have hsclosed : IsClosed S := isClosed_eq hcont continuous_const
  have hsopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro q hqS
    change g q = g p at hqS
    let c := chartAt ℂ q
    have hq : q ∈ c.source := mem_chart_source ℂ q
    have hchart : map c (𝓝 q) = 𝓝 (c q) := c.map_nhds_eq hq
    have hmax : IsLocalMax (fun w : ℂ => g (c.symm w)) (c q) := by
      change ∀ᶠ w in 𝓝 (c q), g (c.symm w) ≤ g (c.symm (c q))
      apply Filter.Eventually.of_forall
      intro w
      simpa only [c.left_inv hq, hqS] using hp (c.symm w)
    have hloc := harmonic_local_max_eq (hg q) hmax
    rw [← hchart] at hloc
    filter_upwards [hloc, c.open_source.mem_nhds hq] with q' he hq'
    change g (c.symm (c q')) = g (c.symm (c q)) at he
    rw [c.left_inv hq', c.left_inv hq] at he
    exact he.trans hqS
  have hsuniv : S = Set.univ := IsClopen.eq_univ ⟨hsclosed, hsopen⟩ ⟨p, rfl⟩
  have hx : g x = g p := by have := Set.mem_univ x; rw [← hsuniv] at this; exact this
  have hy : g y = g p := by have := Set.mem_univ y; rw [← hsuniv] at this; exact this
  exact hx.trans hy.symm

theorem compact_chartwise_harmonic_eq
    (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ∞ E] [CompactSpace E] [PreconnectedSpace E]
    (f : E → ℂ)
    (hf : ∀ q : E,
      HarmonicAt (fun w : ℂ => f ((chartAt ℂ q).symm w))
        ((chartAt ℂ q) q))
    (x y : E) : f x = f y := by
  apply Complex.ext
  · exact compact_chartwise_real_harmonic_eq E (fun q => (f q).re)
      (fun q => by simpa [Function.comp_def] using (hf q).comp_CLM Complex.reCLM) x y
  · exact compact_chartwise_real_harmonic_eq E (fun q => (f q).im)
      (fun q => by simpa [Function.comp_def] using (hf q).comp_CLM Complex.imCLM) x y

end CanonicalDimensionTwo

#print axioms CanonicalDimensionTwo.compact_chartwise_harmonic_eq
