import CurveComplexGenusTwo.Topology.ActualIntervalLocalComparison.ActualOneFormBridge

open scoped Manifold ContDiff Bundle Simplicial
open Bundle
open Convexity
open Filter Topology
open CategoryTheory CategoryTheory.Limits CurveComplexGenusTwo.CWHurewicz
set_option backward.isDefEq.respectTransparency false

namespace CanonicalDimensionTwo

/-!
McMullen, *Riemann Surfaces*, Theorem 6.4, printed p. 56: vanishing
periods give a global primitive, which is constant on a compact surface.
This private leaf uses the actual regular-cycle integral defined above;
it makes no assertion about the triangle-only regular homology quotient.
-/
theorem actualRegularChainIntegral_eq_of_boundary_eq {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E)
    (hs : actualRegularCyclePeriod s = 0)
    (a b : ActualRegularOneChains E)
    (hab : actualRegularChainBoundary a = actualRegularChainBoundary b) :
    actualRegularChainIntegral s a = actualRegularChainIntegral s b := by
  have hcycle : a - b ∈ ActualRegularOneCycles E := by
    change actualRegularChainBoundary (a - b) = 0
    rw [map_sub, sub_eq_zero]
    exact hab
  have hzero := congrArg
    (fun f : ActualRegularOneCycles E →ₗ[ℤ] ℂ => f ⟨a - b, hcycle⟩) hs
  change actualRegularChainIntegral s (a - b) = 0 at hzero
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero

theorem actualRegularPathIntegral_eq_of_endpoints {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E)
    (hs : actualRegularCyclePeriod s = 0)
    (γ δ : ActualRegularPath E)
    (hstart : γ.toFun 0 = δ.toFun 0)
    (hend : γ.toFun 1 = δ.toFun 1) :
    actualPathIntegral s γ.toFun = actualPathIntegral s δ.toFun := by
  have hboundary : actualRegularChainBoundary (Finsupp.single γ 1) =
      actualRegularChainBoundary (Finsupp.single δ 1) := by
    rw [actualRegularChainBoundary_single, actualRegularChainBoundary_single,
      hstart, hend]
  simpa only [actualRegularChainIntegral_single] using
    actualRegularChainIntegral_eq_of_boundary_eq s hs
      (Finsupp.single γ 1) (Finsupp.single δ 1) hboundary

theorem actualChartBallRegularArc_boundary {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (x y : actualChartBallOpenSet q c r) :
    actualRegularChainBoundary
      (Finsupp.single
        (actualChartBallRegularArc q c r htarget
          ⟨(chartAt ℂ q) x.1, x.2.2⟩
          ⟨(chartAt ℂ q) y.1, y.2.2⟩) 1) =
      Finsupp.single y.1 1 - Finsupp.single x.1 1 := by
  rw [actualRegularChainBoundary_single]
  change Finsupp.single
      (actualChartSmoothArc q c r htarget
        ⟨(chartAt ℂ q) x.1, x.2.2⟩
        ⟨(chartAt ℂ q) y.1, y.2.2⟩ 1) 1 -
      Finsupp.single
        (actualChartSmoothArc q c r htarget
          ⟨(chartAt ℂ q) x.1, x.2.2⟩
          ⟨(chartAt ℂ q) y.1, y.2.2⟩ 0) 1 = _
  rw [actualChartSmoothArc_one, actualChartSmoothArc_zero,
    (chartAt ℂ q).left_inv x.2.1, (chartAt ℂ q).left_inv y.2.1]

theorem actualRegularChain_between_points {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    [PreconnectedSpace E] (x y : E) :
    ∃ a : ActualRegularOneChains E,
      actualRegularChainBoundary a =
        Finsupp.single y 1 - Finsupp.single x 1 := by
  let S : Set E := {z | ∃ a : ActualRegularOneChains E,
    actualRegularChainBoundary a =
      Finsupp.single z 1 - Finsupp.single x 1}
  have hlocal (z : E) : ∃ U : Set E, IsOpen U ∧ z ∈ U ∧
      ∀ w ∈ U, ∃ a : ActualRegularOneChains E,
        actualRegularChainBoundary a =
          Finsupp.single w 1 - Finsupp.single z 1 := by
    obtain ⟨r, hr, htarget, hz⟩ := actualChartBallOpenSet_at_point z
    let U := actualChartBallOpenSet z ((chartAt ℂ z) z) r
    refine ⟨U, actualChartBallOpenSet_isOpen z _ r, hz, ?_⟩
    intro w hw
    exact ⟨Finsupp.single
      (actualChartBallRegularArc z ((chartAt ℂ z) z) r htarget
        ⟨(chartAt ℂ z) z, hz.2⟩
        ⟨(chartAt ℂ z) w, hw.2⟩) 1,
      actualChartBallRegularArc_boundary z _ r htarget ⟨z, hz⟩ ⟨w, hw⟩⟩
  have hSopen : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    obtain ⟨U, hU, hzU, hmove⟩ := hlocal z
    apply Filter.mem_of_superset (hU.mem_nhds hzU)
    intro w hw
    obtain ⟨a, ha⟩ := hz
    obtain ⟨b, hb⟩ := hmove w hw
    refine ⟨a + b, ?_⟩
    rw [map_add, ha, hb]
    abel
  have hScopen : IsOpen Sᶜ := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    obtain ⟨U, hU, hzU, hmove⟩ := hlocal z
    apply Filter.mem_of_superset (hU.mem_nhds hzU)
    intro w hw hreach
    obtain ⟨a, ha⟩ := hreach
    obtain ⟨b, hb⟩ := hmove w hw
    apply hz
    refine ⟨a - b, ?_⟩
    rw [map_sub, ha, hb]
    abel
  have hx : x ∈ S := by
    refine ⟨0, ?_⟩
    simp
  have hSuniv : S = Set.univ :=
    (IsClopen.eq_univ ⟨by simpa using hScopen.isClosed_compl, hSopen⟩
      ⟨x, hx⟩)
  change y ∈ S
  rw [hSuniv]
  trivial

noncomputable def actualRegularChainFromBase {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    [PreconnectedSpace E] (x₀ x : E) : ActualRegularOneChains E :=
  Classical.choose (actualRegularChain_between_points x₀ x)

theorem actualRegularChainFromBase_boundary {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    [PreconnectedSpace E] (x₀ x : E) :
    actualRegularChainBoundary (actualRegularChainFromBase x₀ x) =
      Finsupp.single x 1 - Finsupp.single x₀ 1 :=
  Classical.choose_spec (actualRegularChain_between_points x₀ x)

noncomputable def actualGlobalPeriodPrimitive {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    [PreconnectedSpace E] (s : ActualCanonicalSection E) (x₀ x : E) : ℂ :=
  actualRegularChainIntegral s (actualRegularChainFromBase x₀ x)

theorem actualGlobalPeriodPrimitive_path_sub {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    [PreconnectedSpace E] (s : ActualCanonicalSection E)
    (hs : actualRegularCyclePeriod s = 0) (x₀ : E)
    (γ : ActualRegularPath E) :
    actualGlobalPeriodPrimitive s x₀ (γ.toFun 1) -
      actualGlobalPeriodPrimitive s x₀ (γ.toFun 0) =
      actualPathIntegral s γ.toFun := by
  let a := actualRegularChainFromBase x₀ (γ.toFun 1)
  let b := actualRegularChainFromBase x₀ (γ.toFun 0) + Finsupp.single γ 1
  have hab : actualRegularChainBoundary a = actualRegularChainBoundary b := by
    dsimp [a, b]
    rw [map_add, actualRegularChainFromBase_boundary,
      actualRegularChainFromBase_boundary, actualRegularChainBoundary_single]
    abel
  have h := actualRegularChainIntegral_eq_of_boundary_eq s hs a b hab
  simp only [b, map_add, actualRegularChainIntegral_single,
    a, actualGlobalPeriodPrimitive] at h ⊢
  rw [add_comm] at h
  exact sub_eq_iff_eq_add.mpr h

theorem actualGlobalPeriodPrimitive_chartBall_sub {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    [PreconnectedSpace E] (s : ActualCanonicalSection E)
    (hs : actualRegularCyclePeriod s = 0) (x₀ q : E)
    (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (F : ℂ → ℂ)
    (hF : ∀ z ∈ Metric.ball c r,
      HasDerivWithinAt F
        (actualLocalOneForm s q z (fun _ : Fin 1 => (1 : ℂ)))
        (Metric.ball c r) z)
    (x y : actualChartBallOpenSet q c r) :
    actualGlobalPeriodPrimitive s x₀ y.1 -
      actualGlobalPeriodPrimitive s x₀ x.1 =
      F ((chartAt ℂ q) y.1) - F ((chartAt ℂ q) x.1) := by
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
  have hp := actualGlobalPeriodPrimitive_path_sub s hs x₀ γ
  have hi := actualRegularPathIntegral_primitive_sub s γ q c r F
    (actualChartSmoothArc_source q c r htarget z w)
    (actualChartSmoothArc_chart_ball q c r htarget z w) hF
  rw [hγ0, hγ1] at hp hi
  rw [hi] at hp
  exact hp

theorem actualGlobalPeriodPrimitive_mdifferentiable {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    [PreconnectedSpace E] (s : ActualCanonicalSection E)
    (hs : actualRegularCyclePeriod s = 0) (x₀ : E) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (actualGlobalPeriodPrimitive s x₀) := by
  intro x
  obtain ⟨r, hr, htarget, hx⟩ := actualChartBallOpenSet_at_point x
  let U := actualChartBallOpenSet x ((chartAt ℂ x) x) r
  obtain ⟨G, hG⟩ := actualLocalOneForm_has_primitive_on_ball
    s x ((chartAt ℂ x) x) r htarget
  have hGdiff : DifferentiableAt ℂ G ((chartAt ℂ x) x) :=
    (hG _ hx.2).hasDerivAt (Metric.isOpen_ball.mem_nhds hx.2) |>.differentiableAt
  have hchart : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ x) x :=
    mdifferentiableAt_atlas (chart_mem_atlas ℂ x) (mem_chart_source ℂ x)
  have hloc : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
      (fun y : E => G ((chartAt ℂ x) y) +
        (actualGlobalPeriodPrimitive s x₀ x - G ((chartAt ℂ x) x))) x :=
    (hGdiff.mdifferentiableAt.comp x hchart).add mdifferentiableAt_const
  have heq : actualGlobalPeriodPrimitive s x₀ =ᶠ[𝓝 x]
      (fun y : E => G ((chartAt ℂ x) y) +
        (actualGlobalPeriodPrimitive s x₀ x - G ((chartAt ℂ x) x))) := by
    apply Filter.eventually_of_mem
      (actualChartBallOpenSet_isOpen x _ r |>.mem_nhds hx)
    intro y hy
    have hsub := actualGlobalPeriodPrimitive_chartBall_sub s hs x₀ x
      ((chartAt ℂ x) x) r htarget G hG ⟨x, hx⟩ ⟨y, hy⟩
    dsimp at hsub ⊢
    linear_combination hsub
  exact hloc.congr_of_eventuallyEq heq

theorem actualLocalOneForm_coefficient_zero_of_period_zero {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    [CompactSpace E] [PreconnectedSpace E]
    (s : ActualCanonicalSection E)
    (hs : actualRegularCyclePeriod s = 0) (x₀ x : E) :
    actualLocalOneForm s x ((chartAt ℂ x) x)
      (fun _ : Fin 1 => (1 : ℂ)) = 0 := by
  obtain ⟨r, hr, htarget, hx⟩ := actualChartBallOpenSet_at_point x
  obtain ⟨G, hG⟩ := actualLocalOneForm_has_primitive_on_ball
    s x ((chartAt ℂ x) x) r htarget
  have hmd := actualGlobalPeriodPrimitive_mdifferentiable s hs x₀
  have hconst (y : E) : actualGlobalPeriodPrimitive s x₀ y =
      actualGlobalPeriodPrimitive s x₀ x :=
    hmd.apply_eq_of_compactSpace y x
  have hGconst (z : ℂ) (hz : z ∈ Metric.ball ((chartAt ℂ x) x) r) :
      G z = G ((chartAt ℂ x) x) := by
    let y := (chartAt ℂ x).symm z
    have hy : y ∈ actualChartBallOpenSet x ((chartAt ℂ x) x) r := by
      refine ⟨(chartAt ℂ x).map_target (htarget hz), ?_⟩
      simpa [y, (chartAt ℂ x).right_inv (htarget hz)] using hz
    have hsub := actualGlobalPeriodPrimitive_chartBall_sub s hs x₀ x
      ((chartAt ℂ x) x) r htarget G hG ⟨x, hx⟩ ⟨y, hy⟩
    rw [hconst y, sub_self] at hsub
    rw [(chartAt ℂ x).right_inv (htarget hz)] at hsub
    exact sub_eq_zero.mp hsub.symm
  have heq : G =ᶠ[𝓝 ((chartAt ℂ x) x)]
      (fun _ : ℂ => G ((chartAt ℂ x) x)) := by
    exact Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hx.2)
      (fun z hz => hGconst z hz)
  have hderiv : deriv G ((chartAt ℂ x) x) = 0 := by
    rw [heq.deriv_eq]
    simp
  have hcoeff := (hG _ hx.2).hasDerivAt
    (Metric.isOpen_ball.mem_nhds hx.2) |>.deriv
  exact hcoeff.symm.trans hderiv

theorem actualRegularCyclePeriod_injective
    (E : Type) [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (hg : CurveComplex.IsGenus E 2)
    (A : ChartedSpace ℂ E)
    (hA : letI : ChartedSpace ℂ E := A;
      IsManifold 𝓘(ℂ) ∞ E) :
    letI : ChartedSpace ℂ E := A
    Function.Injective (fun s : ActualCanonicalSection E =>
      actualRegularCyclePeriod s) := by
  letI : ChartedSpace ℂ E := A
  letI : IsManifold 𝓘(ℂ) ∞ E := hA
  letI : CurveComplex.ClosedSurface E := Classical.choice hg.2.1
  letI : PreconnectedSpace E := inferInstance
  intro s t hst
  have hperiod : actualRegularCyclePeriod (s - t) = 0 := by
    apply LinearMap.ext
    intro c
    have hc := congrArg
      (fun f : ActualRegularOneCycles E →ₗ[ℤ] ℂ => f c) hst
    change actualRegularChainIntegral (s - t) c.1 = 0
    have hsub : actualRegularChainIntegral (s - t) =
        actualRegularChainIntegral s - actualRegularChainIntegral t :=
      map_sub (actualRegularPeriod (E := E)) s t
    rw [hsub, LinearMap.sub_apply, sub_eq_zero]
    exact hc
  have hzero : s - t = 0 := by
    apply ContMDiffSection.ext
    intro x
    apply ContinuousLinearMap.ext
    intro v
    let x₀ : E := Classical.choice hg.1
    have hc := actualLocalOneForm_coefficient_zero_of_period_zero
      (s - t) hperiod x₀ x
    have hv := actualLocalOneForm_eq_global_on_tangent (s - t) x x v
      (mem_chart_source ℂ x)
    rw [actualLocalOneForm_apply_eq_mul_coefficient, hc, mul_zero] at hv
    simpa [actualOneForm] using hv.symm
  exact sub_eq_zero.mp hzero

end CanonicalDimensionTwo
