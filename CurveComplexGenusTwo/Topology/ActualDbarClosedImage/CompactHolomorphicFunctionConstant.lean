import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.LocallyConstant.Basic

open Filter Topology Set

namespace CanonicalBasepointFree

private theorem compact_open_map_surjective
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    [TopologicalSpace Y] [T2Space Y] [PreconnectedSpace Y]
    {f : X → Y} (hf : Continuous f) (ho : IsOpenMap f) :
    Function.Surjective f := by
  have hclosed : IsClosed (Set.range f) := (isCompact_range hf).isClosed
  have hopen : IsOpen (Set.range f) := ho.isOpen_range
  have hn : (Set.range f).Nonempty := ⟨f (Classical.choice inferInstance),
    Set.mem_range_self _⟩
  have htop := (IsClopen.eq_univ ⟨hclosed, hopen⟩ hn)
  exact Set.range_eq_univ.mp htop

private theorem chart_analytic_nonconstant_locally_open
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    (x : E) (f : E → ℂ) (a : ℂ → ℂ)
    (ha : AnalyticAt ℂ a ((chartAt ℂ x) x))
    (hlocal : f =ᶠ[𝓝 x] fun y => a ((chartAt ℂ x) y))
    (hpoint : f x = a ((chartAt ℂ x) x))
    (hnonconstant : ¬ ∀ᶠ z in 𝓝 ((chartAt ℂ x) x),
      a z = a ((chartAt ℂ x) x)) :
    𝓝 (f x) ≤ map f (𝓝 x) := by
  let c := chartAt ℂ x
  have hx : x ∈ c.source := mem_chart_source ℂ x
  have hchart : map c (𝓝 x) = 𝓝 (c x) := c.map_nhds_eq hx
  have hopen : 𝓝 (a (c x)) ≤ map a (𝓝 (c x)) :=
    ha.eventually_constant_or_nhds_le_map_nhds_aux.resolve_left hnonconstant
  rw [hpoint]
  rw [← hchart] at hopen
  calc
    𝓝 (a (c x)) ≤ map (a ∘ c) (𝓝 x) := by simpa [map_map] using hopen
    _ = map f (𝓝 x) := (map_congr hlocal).symm

private theorem compact_surface_no_everywhere_locally_nonconstant_holomorphic_map
    {E : Type*} [TopologicalSpace E] [T2Space E]
    [CompactSpace E] [Nonempty E] [ChartedSpace ℂ E]
    (f : E → ℂ) (hf : Continuous f)
    (hreg : ∀ x : E, ∃ a : ℂ → ℂ,
      AnalyticAt ℂ a ((chartAt ℂ x) x) ∧
      (f =ᶠ[𝓝 x] fun y => a ((chartAt ℂ x) y)) ∧
      f x = a ((chartAt ℂ x) x) ∧
      ¬ ∀ᶠ z in 𝓝 ((chartAt ℂ x) x), a z = a ((chartAt ℂ x) x)) :
    False := by
  have ho : IsOpenMap f := by
    apply isOpenMap_iff_nhds_le.mpr
    intro x
    obtain ⟨a, ha, hlocal, hpoint, hnonconstant⟩ := hreg x
    exact chart_analytic_nonconstant_locally_open x f a ha hlocal hpoint hnonconstant
  have hsurj : Function.Surjective f := compact_open_map_surjective hf ho
  have hcompact : IsCompact (Set.univ : Set ℂ) := by
    simpa [Set.range_eq_univ.mpr hsurj] using isCompact_range hf
  exact (not_compactSpace_iff.mpr inferInstance) (isCompact_univ_iff.mp hcompact)

private theorem analyticAt_eventually_not_locally_constant
    (a : ℂ → ℂ) (z₀ : ℂ) (ha : AnalyticAt ℂ a z₀)
    (hnonconstant : ¬ ∀ᶠ z in 𝓝 z₀, a z = a z₀) :
    ∀ᶠ z in 𝓝 z₀, ¬ ∀ᶠ w in 𝓝 z, a w = a z := by
  obtain ⟨r, hr, hball⟩ := ha.exists_ball_analyticOnNhd
  apply Filter.Eventually.mono (Metric.ball_mem_nhds z₀ hr)
  intro z hz hconst
  have hconstAnalytic : AnalyticOnNhd ℂ (fun _ : ℂ => a z) (Metric.ball z₀ r) :=
    fun _ _ => analyticAt_const
  have hEq : Set.EqOn a (fun _ : ℂ => a z) (Metric.ball z₀ r) :=
    hball.eqOn_of_preconnected_of_eventuallyEq hconstAnalytic
      (convex_ball z₀ r).isPreconnected hz hconst
  have hz₀ : a z₀ = a z := hEq (Metric.mem_ball_self hr)
  apply hnonconstant
  filter_upwards [Metric.ball_mem_nhds z₀ hr] with w hw
  exact (hEq hw).trans hz₀.symm

private theorem surface_chart_eventually_constant_iff
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    (x : E) (f : E → ℂ) (a : ℂ → ℂ)
    (hlocal : f =ᶠ[𝓝 x] fun y => a ((chartAt ℂ x) y))
    (hpoint : f x = a ((chartAt ℂ x) x)) :
    (∀ᶠ y in 𝓝 x, f y = f x) ↔
      ∀ᶠ z in 𝓝 ((chartAt ℂ x) x), a z = a ((chartAt ℂ x) x) := by
  let c := chartAt ℂ x
  have hx : x ∈ c.source := mem_chart_source ℂ x
  have hcx : c x ∈ c.target := c.map_source hx
  have hchart : map c (𝓝 x) = 𝓝 (c x) := c.map_nhds_eq hx
  constructor
  · intro hconst
    have hs : (fun y => a (c y)) =ᶠ[𝓝 x] (fun _ => a (c x)) := by
      filter_upwards [hlocal, hconst] with y hfy hcy
      rw [← hfy, hcy, hpoint]
    have hsymm : Tendsto c.symm (𝓝 (c x)) (𝓝 x) := by
      simpa [c.left_inv hx] using (c.symm.continuousAt hcx).tendsto
    have ht : ∀ᶠ z in 𝓝 (c x), z ∈ c.target := c.open_target.mem_nhds hcx
    filter_upwards [hs.comp_tendsto hsymm, ht] with z hz hzt
    simpa [c.right_inv hzt] using hz
  · intro hconst
    have hs : (fun y => a (c y)) =ᶠ[𝓝 x] (fun _ => a (c x)) := by
      rw [← hchart] at hconst
      exact hconst
    filter_upwards [hlocal, hs] with y hfy hcy
    rw [hfy, hcy, hpoint]

private theorem surface_chart_eventually_not_locally_constant
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    (x : E) (f : E → ℂ) (a : ℂ → ℂ)
    (ha : AnalyticAt ℂ a ((chartAt ℂ x) x))
    (hlocal : f =ᶠ[𝓝 x] fun y => a ((chartAt ℂ x) y))
    (hnonconstant : ¬ ∀ᶠ z in 𝓝 ((chartAt ℂ x) x),
      a z = a ((chartAt ℂ x) x)) :
    ∀ᶠ y in 𝓝 x, ¬ ∀ᶠ z in 𝓝 y, f z = f y := by
  let c := chartAt ℂ x
  have hx : x ∈ c.source := mem_chart_source ℂ x
  have hnearAnalytic :=
    (c.continuousAt hx).tendsto.eventually
      (analyticAt_eventually_not_locally_constant a (c x) ha hnonconstant)
  have hnearLocal : ∀ᶠ y in 𝓝 x,
      f =ᶠ[𝓝 y] fun z => a (c z) :=
    isOpen_setOfPred_eventually_nhds.mem_nhds hlocal
  filter_upwards [hnearAnalytic, hnearLocal, c.open_source.mem_nhds hx]
    with y hnot hlocaly hy hconst
  have hpointy : f y = a (c y) := hlocaly.eq_of_nhds
  have hconstChart : ∀ᶠ z in 𝓝 y, a (c z) = a (c y) := by
    filter_upwards [hlocaly, hconst] with z hz hcz
    rw [← hz, hcz, hpointy]
  have hconstA : ∀ᶠ z in 𝓝 (c y), a z = a (c y) := by
    rw [← c.map_nhds_eq hy]
    exact hconstChart
  exact hnot hconstA

private theorem surface_global_analytic_constant_or_nowhere_locally_constant
    {E : Type*} [TopologicalSpace E] [PreconnectedSpace E]
    [ChartedSpace ℂ E] (f : E → ℂ)
    (hreg : ∀ x : E, ∃ a : ℂ → ℂ,
      AnalyticAt ℂ a ((chartAt ℂ x) x) ∧
      (f =ᶠ[𝓝 x] fun y => a ((chartAt ℂ x) y)) ∧
      f x = a ((chartAt ℂ x) x)) :
    (∀ x y : E, f x = f y) ∨
      ∀ x : E, ¬ ∀ᶠ y in 𝓝 x, f y = f x := by
  let S : Set E := {x | ∀ᶠ y in 𝓝 x, f y = f x}
  have hopenS : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have ho : IsOpen {y : E | ∀ᶠ z in 𝓝 y, f z = f x} :=
      isOpen_setOfPred_eventually_nhds
    apply Filter.mem_of_superset (ho.mem_nhds hx)
    intro y hy
    have hxy : f y = f x := hy.self_of_nhds
    simpa [S, hxy] using hy
  have hopenC : IsOpen Sᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨a, ha, hlocal, hpoint⟩ := hreg x
    have hnonconstant : ¬ ∀ᶠ z in 𝓝 ((chartAt ℂ x) x),
        a z = a ((chartAt ℂ x) x) := by
      intro hconst
      exact hx ((surface_chart_eventually_constant_iff x f a hlocal hpoint).2 hconst)
    exact surface_chart_eventually_not_locally_constant x f a ha hlocal hnonconstant
  by_cases hS : S.Nonempty
  · have hclosedS : IsClosed S := by simpa using hopenC.isClosed_compl
    have htop : S = Set.univ := IsClopen.eq_univ ⟨hclosedS, hopenS⟩ hS
    left
    apply IsLocallyConstant.iff_is_const.mp
    apply (IsLocallyConstant.iff_eventually_eq f).2
    intro x
    have hx : x ∈ S := by rw [htop]; trivial
    exact hx
  · right
    intro x hx
    exact hS ⟨x, hx⟩

theorem compact_surface_global_analytic_map_constant
    {E : Type*} [TopologicalSpace E] [T2Space E]
    [CompactSpace E] [Nonempty E] [PreconnectedSpace E]
    [ChartedSpace ℂ E] (f : E → ℂ)
    (hreg : ∀ x : E, ∃ a : ℂ → ℂ,
      AnalyticAt ℂ a ((chartAt ℂ x) x) ∧
      (f =ᶠ[𝓝 x] fun y => a ((chartAt ℂ x) y)) ∧
      f x = a ((chartAt ℂ x) x)) :
    ∀ x y : E, f x = f y := by
  have hf : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro x
    obtain ⟨a, ha, hlocal, _⟩ := hreg x
    have hchart : ContinuousAt (chartAt ℂ x) x :=
      (chartAt ℂ x).continuousAt (mem_chart_source ℂ x)
    exact (ha.continuousAt.comp hchart).congr_of_eventuallyEq hlocal
  rcases surface_global_analytic_constant_or_nowhere_locally_constant f hreg with h | h
  · exact h
  · exact False.elim <| compact_surface_no_everywhere_locally_nonconstant_holomorphic_map
      f hf (fun x => by
        obtain ⟨a, ha, hlocal, hpoint⟩ := hreg x
        refine ⟨a, ha, hlocal, hpoint, ?_⟩
        intro hconst
        exact h x ((surface_chart_eventually_constant_iff x f a hlocal hpoint).2 hconst))

end CanonicalBasepointFree

#print axioms CanonicalBasepointFree.compact_surface_global_analytic_map_constant
