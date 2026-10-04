import CurveComplexGenusTwo.Topology.ActualCanonicalDimensionTwo.ActualMixedPrimitiveCanonical85
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.FDeriv.Star

open scoped Topology
open scoped Manifold ContDiff Bundle

namespace CanonicalDimensionTwo

theorem holomorphic_add_conj_deriv_zero_of_eventually_const
    (F G : ℂ → ℂ) (z : ℂ)
    (hF : DifferentiableAt ℂ F z)
    (hG : DifferentiableAt ℂ G z)
    (c : ℂ)
    (hconst : (fun w : ℂ => F w + star (G w)) =ᶠ[𝓝 z]
      (fun _ => c)) :
    deriv F z = 0 ∧ deriv G z = 0 := by
  let a := deriv F z
  let b := deriv G z
  have hF' : HasFDerivAt F (ContinuousLinearMap.toSpanSingleton ℂ a) z :=
    hF.hasDerivAt.hasFDerivAt
  have hG' : HasFDerivAt G (ContinuousLinearMap.toSpanSingleton ℂ b) z :=
    hG.hasDerivAt.hasFDerivAt
  have hsum : HasFDerivAt (fun w : ℂ => F w + star (G w))
      ((ContinuousLinearMap.toSpanSingleton ℂ a).restrictScalars ℝ +
        (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.comp
          ((ContinuousLinearMap.toSpanSingleton ℂ b).restrictScalars ℝ)) z := by
    exact (hF'.restrictScalars ℝ).add
      ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ).hasFDerivAt.comp z
        (hG'.restrictScalars ℝ))
  have hzero : HasFDerivAt (fun w : ℂ => F w + star (G w))
      (0 : ℂ →L[ℝ] ℂ) z := by
    exact (hasFDerivAt_const c z).congr_of_eventuallyEq hconst
  have heq := hsum.unique hzero
  have h1 := congrArg (fun L : ℂ →L[ℝ] ℂ => L 1) heq
  have hI := congrArg (fun L : ℂ →L[ℝ] ℂ => L Complex.I) heq
  simp [a, b] at h1 hI
  have ha2 : (2 * Complex.I) * deriv F z = 0 := by
    linear_combination Complex.I * h1 + hI
  have ha : deriv F z = 0 :=
    (mul_eq_zero.mp ha2).resolve_left (by norm_num)
  have hb : deriv G z = 0 := by
    simpa [ha] using h1
  exact ⟨ha, hb⟩

theorem actualMixedGlobalPrimitive_coefficients_zero_of_constancy {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    [PreconnectedSpace E]
    (s t : ActualCanonicalSection E)
    (hzero : ∀ z : ActualRegularOneCycles E,
      actualRegularCyclePeriod s z +
        star (actualRegularCyclePeriod t z) = 0)
    (x₀ : E)
    (hconst : ∀ x : E,
      actualMixedGlobalPrimitive s t x₀ x =
        actualMixedGlobalPrimitive s t x₀ x₀)
    (q : E) :
    actualLocalOneForm s q ((chartAt ℂ q) q)
      (fun _ : Fin 1 => (1 : ℂ)) = 0 ∧
    actualLocalOneForm t q ((chartAt ℂ q) q)
      (fun _ : Fin 1 => (1 : ℂ)) = 0 := by
  obtain ⟨r, hr, htarget, hq⟩ := actualChartBallOpenSet_at_point q
  obtain ⟨F, hF⟩ := actualLocalOneForm_has_primitive_on_ball
    s q ((chartAt ℂ q) q) r htarget
  obtain ⟨G, hG⟩ := actualLocalOneForm_has_primitive_on_ball
    t q ((chartAt ℂ q) q) r htarget
  let z := (chartAt ℂ q) q
  have hz : z ∈ Metric.ball z r := hq.2
  let y : actualChartBallOpenSet q z r := ⟨q, hq⟩
  have hnear : (fun w : ℂ => F w + star (G w)) =ᶠ[𝓝 z]
      (fun _ => F z + star (G z)) := by
    apply Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hz)
    intro w hw
    let yw : actualChartBallOpenSet q z r :=
      ⟨(chartAt ℂ q).symm w, (chartAt ℂ q).map_target (htarget hw),
        by simpa [(chartAt ℂ q).right_inv (htarget hw)] using hw⟩
    have hsub := actualMixedGlobalPrimitive_chartBall_sub
      s t hzero x₀ q z r htarget F G hF hG y yw
    have hglobal : actualMixedGlobalPrimitive s t x₀ yw.1 -
        actualMixedGlobalPrimitive s t x₀ y.1 = 0 := by
      rw [hconst yw.1, hconst y.1, sub_self]
    rw [hglobal] at hsub
    dsimp [y, yw, z] at hsub ⊢
    rw [(chartAt ℂ q).right_inv (htarget hw)] at hsub
    simp only [map_sub] at hsub
    linear_combination -hsub
  have hFd : DifferentiableAt ℂ F z :=
    (hF z hz).hasDerivAt (Metric.isOpen_ball.mem_nhds hz) |>.differentiableAt
  have hGd : DifferentiableAt ℂ G z :=
    (hG z hz).hasDerivAt (Metric.isOpen_ball.mem_nhds hz) |>.differentiableAt
  obtain ⟨hFzero, hGzero⟩ :=
    holomorphic_add_conj_deriv_zero_of_eventually_const
      F G z hFd hGd (F z + star (G z)) hnear
  have hFderiv :=
    (hF z hz).hasDerivAt (Metric.isOpen_ball.mem_nhds hz) |>.deriv
  have hGderiv :=
    (hG z hz).hasDerivAt (Metric.isOpen_ball.mem_nhds hz) |>.deriv
  exact ⟨hFderiv.symm.trans hFzero, hGderiv.symm.trans hGzero⟩

theorem actualHodgePeriod_injective_of_chartwise_harmonic_constancy
    (E : Type) [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (hg : CurveComplex.IsGenus E 2)
    (A : ChartedSpace ℂ E)
    (hA : letI : ChartedSpace ℂ E := A;
      IsManifold 𝓘(ℂ) ∞ E)
    (hHarmonic : letI : ChartedSpace ℂ E := A
      letI : IsManifold 𝓘(ℂ) ∞ E := hA
      ∀ (f : E → ℂ),
        (∀ q : E,
          InnerProductSpace.HarmonicAt
            (fun w : ℂ => f ((chartAt ℂ q).symm w))
            ((chartAt ℂ q) q)) →
        ∀ x y : E, f x = f y) :
    letI : ChartedSpace ℂ E := A
    letI : IsManifold 𝓘(ℂ) ∞ E := hA
    Function.Injective (actualHodgePeriod (E := E)) := by
  letI : ChartedSpace ℂ E := A
  letI : IsManifold 𝓘(ℂ) ∞ E := hA
  letI : CurveComplex.ClosedSurface E := Classical.choice hg.2.1
  letI : PreconnectedSpace E := inferInstance
  apply LinearMap.ker_eq_bot.mp
  rw [eq_bot_iff]
  intro p hp
  rw [LinearMap.mem_ker] at hp
  have hzero :=
    (actualHodgePeriod_zero_iff_regular_cycle p.1 p.2).mp hp
  let x₀ : E := Classical.choice hg.1
  have hconst : ∀ x : E,
      actualMixedGlobalPrimitive p.1 p.2 x₀ x =
        actualMixedGlobalPrimitive p.1 p.2 x₀ x₀ :=
    fun x => hHarmonic (actualMixedGlobalPrimitive p.1 p.2 x₀)
      (actualMixedGlobalPrimitive_harmonicAt_at p.1 p.2 hzero x₀)
      x x₀
  have hzeroS : p.1 = 0 := by
    apply ContMDiffSection.ext
    intro x
    apply ContinuousLinearMap.ext
    intro v
    have hc :=
      (actualMixedGlobalPrimitive_coefficients_zero_of_constancy
        p.1 p.2 hzero x₀ hconst x).1
    have hv := actualLocalOneForm_eq_global_on_tangent p.1 x x v
      (mem_chart_source ℂ x)
    rw [actualLocalOneForm_apply_eq_mul_coefficient, hc, mul_zero] at hv
    simpa [actualOneForm] using hv.symm
  have hzeroT : p.2 = 0 := by
    apply ContMDiffSection.ext
    intro x
    apply ContinuousLinearMap.ext
    intro v
    have hc :=
      (actualMixedGlobalPrimitive_coefficients_zero_of_constancy
        p.1 p.2 hzero x₀ hconst x).2
    have hv := actualLocalOneForm_eq_global_on_tangent p.2 x x v
      (mem_chart_source ℂ x)
    rw [actualLocalOneForm_apply_eq_mul_coefficient, hc, mul_zero] at hv
    simpa [actualOneForm] using hv.symm
  have hpzero : p = 0 := by
    cases p with
    | mk s t =>
      simpa using (Prod.ext hzeroS hzeroT : (s, t) = (0, 0))
  exact hpzero ▸ Submodule.zero_mem _

end CanonicalDimensionTwo
