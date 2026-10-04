import CurveComplexGenusTwo.Topology.ActualCanonicalDimensionTwo.ActualHodgeKernelCanonical85
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

open scoped Manifold ContDiff Bundle Simplicial TensorProduct Topology
open CanonicalDimensionTwo
open InnerProductSpace

namespace CanonicalDimensionTwo

noncomputable def actualMixedChainIntegral {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s t : ActualCanonicalSection E) : ActualRegularOneChains E →ₗ[ℤ] ℂ where
  toFun a := actualRegularChainIntegral s a + star (actualRegularChainIntegral t a)
  map_add' a b := by simp [map_add, star_add, add_add_add_comm]
  map_smul' n a := by simp

theorem actualMixedChainIntegral_cycle {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s t : ActualCanonicalSection E) (z : ActualRegularOneCycles E) :
    actualMixedChainIntegral s t z.1 =
      actualRegularCyclePeriod s z + star (actualRegularCyclePeriod t z) := rfl

theorem actualMixedChainIntegral_eq_of_boundary_eq {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s t : ActualCanonicalSection E)
    (hzero : ∀ z : ActualRegularOneCycles E,
      actualRegularCyclePeriod s z +
        star (actualRegularCyclePeriod t z) = 0)
    (a b : ActualRegularOneChains E)
    (hab : actualRegularChainBoundary a = actualRegularChainBoundary b) :
    actualMixedChainIntegral s t a = actualMixedChainIntegral s t b := by
  have hcycle : a - b ∈ ActualRegularOneCycles E := by
    change actualRegularChainBoundary (a - b) = 0
    rw [map_sub, sub_eq_zero]
    exact hab
  have h := hzero ⟨a - b, hcycle⟩
  change actualMixedChainIntegral s t (a - b) = 0 at h
  rw [map_sub, sub_eq_zero] at h
  exact h

noncomputable def actualMixedGlobalPrimitive {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    [PreconnectedSpace E]
    (s t : ActualCanonicalSection E) (x₀ x : E) : ℂ :=
  actualMixedChainIntegral s t (actualRegularChainFromBase x₀ x)

theorem actualMixedGlobalPrimitive_path_sub {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    [PreconnectedSpace E]
    (s t : ActualCanonicalSection E)
    (hzero : ∀ z : ActualRegularOneCycles E,
      actualRegularCyclePeriod s z +
        star (actualRegularCyclePeriod t z) = 0)
    (x₀ : E) (γ : ActualRegularPath E) :
    actualMixedGlobalPrimitive s t x₀ (γ.toFun 1) -
      actualMixedGlobalPrimitive s t x₀ (γ.toFun 0) =
      actualPathIntegral s γ.toFun + star (actualPathIntegral t γ.toFun) := by
  let a := actualRegularChainFromBase x₀ (γ.toFun 1)
  let b := actualRegularChainFromBase x₀ (γ.toFun 0) + Finsupp.single γ 1
  have hab : actualRegularChainBoundary a = actualRegularChainBoundary b := by
    dsimp [a, b]
    rw [map_add, actualRegularChainFromBase_boundary,
      actualRegularChainFromBase_boundary, actualRegularChainBoundary_single]
    abel
  have h := actualMixedChainIntegral_eq_of_boundary_eq s t hzero a b hab
  simp only [b, map_add, a, actualMixedGlobalPrimitive] at h ⊢
  have hsingle : actualMixedChainIntegral s t (Finsupp.single γ 1) =
      actualPathIntegral s γ.toFun + star (actualPathIntegral t γ.toFun) := by
    simp [actualMixedChainIntegral, actualRegularChainIntegral_single]
  rw [hsingle] at h
  change actualMixedChainIntegral s t
    (actualRegularChainFromBase x₀ (γ.toFun 1)) =
    actualMixedChainIntegral s t
      (actualRegularChainFromBase x₀ (γ.toFun 0)) +
      (actualPathIntegral s γ.toFun + star (actualPathIntegral t γ.toFun)) at h
  exact sub_eq_iff_eq_add.mpr (h.trans (add_comm _ _))

theorem actualMixedGlobalPrimitive_chartBall_sub {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    [PreconnectedSpace E]
    (s t : ActualCanonicalSection E)
    (hzero : ∀ z : ActualRegularOneCycles E,
      actualRegularCyclePeriod s z +
        star (actualRegularCyclePeriod t z) = 0)
    (x₀ q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (F G : ℂ → ℂ)
    (hF : ∀ z ∈ Metric.ball c r,
      HasDerivWithinAt F
        (actualLocalOneForm s q z (fun _ : Fin 1 => (1 : ℂ)))
        (Metric.ball c r) z)
    (hG : ∀ z ∈ Metric.ball c r,
      HasDerivWithinAt G
        (actualLocalOneForm t q z (fun _ : Fin 1 => (1 : ℂ)))
        (Metric.ball c r) z)
    (x y : actualChartBallOpenSet q c r) :
    actualMixedGlobalPrimitive s t x₀ y.1 -
      actualMixedGlobalPrimitive s t x₀ x.1 =
      (F ((chartAt ℂ q) y.1) - F ((chartAt ℂ q) x.1)) +
        star (G ((chartAt ℂ q) y.1) - G ((chartAt ℂ q) x.1)) := by
  let z : Metric.ball c r := ⟨(chartAt ℂ q) x.1, x.2.2⟩
  let w : Metric.ball c r := ⟨(chartAt ℂ q) y.1, y.2.2⟩
  let γ := actualChartBallRegularArc q c r htarget z w
  have hγ0 : γ.toFun 0 = x.1 := by
    change actualChartSmoothArc q c r htarget z w 0 = x.1
    rw [actualChartSmoothArc_zero]
    exact (chartAt ℂ q).left_inv x.2.1
  have hγ1 : γ.toFun 1 = y.1 := by
    change actualChartSmoothArc q c r htarget z w 1 = y.1
    rw [actualChartSmoothArc_one]
    exact (chartAt ℂ q).left_inv y.2.1
  have hp := actualMixedGlobalPrimitive_path_sub s t hzero x₀ γ
  have his := actualRegularPathIntegral_primitive_sub s γ q c r F
    (actualChartSmoothArc_source q c r htarget z w)
    (actualChartSmoothArc_chart_ball q c r htarget z w) hF
  have hit := actualRegularPathIntegral_primitive_sub t γ q c r G
    (actualChartSmoothArc_source q c r htarget z w)
    (actualChartSmoothArc_chart_ball q c r htarget z w) hG
  rw [hγ0, hγ1] at hp his hit
  rw [his, hit] at hp
  exact hp

theorem harmonicAt_holomorphic_add_conj
    (F G : ℂ → ℂ) (c : ℂ) (r : ℝ)
    (hF : DifferentiableOn ℂ F (Metric.ball c r))
    (hG : DifferentiableOn ℂ G (Metric.ball c r))
    (z : ℂ) (hz : z ∈ Metric.ball c r) :
    HarmonicAt (fun w : ℂ => F w + star (G w)) z := by
  have hFn : AnalyticAt ℂ F z :=
    hF.analyticAt (Metric.isOpen_ball.mem_nhds hz)
  have hGn : AnalyticAt ℂ G z :=
    hG.analyticAt (Metric.isOpen_ball.mem_nhds hz)
  exact hFn.harmonicAt.add hGn.harmonicAt_conj

theorem actualMixedGlobalPrimitive_chart_harmonicAt {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    [PreconnectedSpace E]
    (s t : ActualCanonicalSection E)
    (hzero : ∀ z : ActualRegularOneCycles E,
      actualRegularCyclePeriod s z +
        star (actualRegularCyclePeriod t z) = 0)
    (x₀ q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (F G : ℂ → ℂ)
    (hF : ∀ z ∈ Metric.ball c r,
      HasDerivWithinAt F
        (actualLocalOneForm s q z (fun _ : Fin 1 => (1 : ℂ)))
        (Metric.ball c r) z)
    (hG : ∀ z ∈ Metric.ball c r,
      HasDerivWithinAt G
        (actualLocalOneForm t q z (fun _ : Fin 1 => (1 : ℂ)))
        (Metric.ball c r) z)
    (z : ℂ) (hz : z ∈ Metric.ball c r) :
    HarmonicAt
      (fun w : ℂ => actualMixedGlobalPrimitive s t x₀ ((chartAt ℂ q).symm w)) z := by
  let y : actualChartBallOpenSet q c r :=
    ⟨(chartAt ℂ q).symm z, (chartAt ℂ q).map_target (htarget hz),
      by simpa [(chartAt ℂ q).right_inv (htarget hz)] using hz⟩
  let K : ℂ := actualMixedGlobalPrimitive s t x₀ y.1 -
    (F z + star (G z))
  have hnear : (fun w : ℂ =>
      actualMixedGlobalPrimitive s t x₀ ((chartAt ℂ q).symm w)) =ᶠ[𝓝 z]
      (fun w : ℂ => F w + star (G w) + K) := by
    apply Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hz)
    intro w hw
    let yw : actualChartBallOpenSet q c r :=
      ⟨(chartAt ℂ q).symm w, (chartAt ℂ q).map_target (htarget hw),
        by simpa [(chartAt ℂ q).right_inv (htarget hw)] using hw⟩
    have hsub := actualMixedGlobalPrimitive_chartBall_sub
      s t hzero x₀ q c r htarget F G hF hG y yw
    dsimp [y, yw, K] at hsub ⊢
    rw [(chartAt ℂ q).right_inv (htarget hz),
      (chartAt ℂ q).right_inv (htarget hw)] at hsub
    simp only [map_sub] at hsub
    linear_combination hsub
  have hFd : DifferentiableOn ℂ F (Metric.ball c r) :=
    fun w hw => (hF w hw).differentiableWithinAt
  have hGd : DifferentiableOn ℂ G (Metric.ball c r) :=
    fun w hw => (hG w hw).differentiableWithinAt
  have hlocal : HarmonicAt (fun w : ℂ => F w + star (G w) + K) z :=
    (harmonicAt_holomorphic_add_conj F G c r hFd hGd z hz).add (harmonicAt_const K)
  exact (harmonicAt_congr_nhds hnear).2 hlocal

theorem actualMixedGlobalPrimitive_harmonicAt_at {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    [PreconnectedSpace E]
    (s t : ActualCanonicalSection E)
    (hzero : ∀ z : ActualRegularOneCycles E,
      actualRegularCyclePeriod s z +
        star (actualRegularCyclePeriod t z) = 0)
    (x₀ q : E) :
    HarmonicAt
      (fun w : ℂ => actualMixedGlobalPrimitive s t x₀ ((chartAt ℂ q).symm w))
      ((chartAt ℂ q) q) := by
  obtain ⟨r, hr, htarget, hq⟩ := actualChartBallOpenSet_at_point q
  obtain ⟨F, hF⟩ := actualLocalOneForm_has_primitive_on_ball
    s q ((chartAt ℂ q) q) r htarget
  obtain ⟨G, hG⟩ := actualLocalOneForm_has_primitive_on_ball
    t q ((chartAt ℂ q) q) r htarget
  exact actualMixedGlobalPrimitive_chart_harmonicAt s t hzero x₀ q
    ((chartAt ℂ q) q) r htarget F G hF hG _ hq.2

end CanonicalDimensionTwo
