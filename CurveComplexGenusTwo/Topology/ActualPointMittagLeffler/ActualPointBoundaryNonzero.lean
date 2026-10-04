import CurveComplexGenusTwo.Topology.ActualLocalAnalyticSheaves.LocalSheafScaffold

open scoped Manifold ContDiff Bundle
open Bundle Filter Topology
open SameAtlasRRLocal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace CanonicalDimensionTwo

private theorem actualSurfaceChartMeromorphicGermUnique
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    (x : E) (f : E → ℂ) (a b : ℂ → ℂ)
    (ha : f =ᶠ[𝓝[≠] x] fun y => a ((chartAt ℂ x) y))
    (hb : f =ᶠ[𝓝[≠] x] fun y => b ((chartAt ℂ x) y)) :
    a =ᶠ[𝓝[≠] ((chartAt ℂ x) x)] b := by
  let c := chartAt ℂ x
  have hx : x ∈ c.source := mem_chart_source ℂ x
  have hcx : c x ∈ c.target := c.map_source hx
  have hcsymm0 : Tendsto c.symm (𝓝[≠] (c x))
      (𝓝[≠] (c.symm (c x))) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨(c.symm.continuousAt hcx).tendsto.mono_left nhdsWithin_le_nhds,
        c.symm.eventually_ne_nhdsWithin hcx⟩
  have hcsymm : Tendsto c.symm (𝓝[≠] (c x)) (𝓝[≠] x) := by
    simpa [c.left_inv hx] using hcsymm0
  have h12 : (fun y => a (c y)) =ᶠ[𝓝[≠] x] fun y => b (c y) :=
    ha.symm.trans hb
  have h12' := h12.comp_tendsto hcsymm
  have ht : ∀ᶠ z in 𝓝[≠] (c x), z ∈ c.target :=
    nhdsWithin_le_nhds (c.open_target.mem_nhds hcx)
  filter_upwards [h12', ht] with z hz hzt
  simpa [c.right_inv hzt] using hz


private theorem actualDivisorOrder_eq_chart_order
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    (F : SurfaceMeromorphicFunction E) (x : E) (a : ℂ → ℂ)
    (ha : F.toFun =ᶠ[𝓝[≠] x] fun y => a ((chartAt ℂ x) y)) :
    F.divisorOrder x = meromorphicOrderAt a ((chartAt ℂ x) x) := by
  exact meromorphicOrderAt_congr (actualSurfaceChartMeromorphicGermUnique x F.toFun
    (Classical.choose (F.meromorphicAt x)) a (Classical.choose_spec (F.meromorphicAt x)).2 ha)


/-- Convert the literal whole-surface simple-pole section to the existing
surface meromorphic carrier. This is the old same-atlas RR conversion,
now expressed directly using the public sheaf coefficient. -/
theorem actualGlobalPole_nonzero_coefficient_gives_simple_pole
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ∞ E] (p : E) (f : PoleOneOn p ⊤)
    (hf : coeffAt p ⊤ trivial f ≠ 0) :
    ∃ F : SurfaceMeromorphicFunction E,
      F.divisorOrder p = (-1 : ℤ) ∧
      (∀ x : E, x ≠ p → ∃ a : ℂ → ℂ,
        AnalyticAt ℂ a ((chartAt ℂ x) x) ∧
        (F.toFun =ᶠ[𝓝 x] fun y => a ((chartAt ℂ x) y)) ∧
        F.toFun x = a ((chartAt ℂ x) x)) := by
  classical
  letI : T1Space E := ChartedSpace.t1Space ℂ E
  let a := Classical.choose (f.property.2 trivial)
  let z₀ := (chartAt ℂ p) p
  let F : E → ℂ := fun y => if hy : y = p then 0 else f.1 ⟨⟨y, trivial⟩, hy⟩
  have hreg : ∀ x : E, x ≠ p → ∃ b : ℂ → ℂ,
      AnalyticAt ℂ b ((chartAt ℂ x) x) ∧
      (F =ᶠ[𝓝 x] fun y => b ((chartAt ℂ x) y)) ∧
      F x = b ((chartAt ℂ x) x) := by
    intro x hx
    obtain ⟨b, hb, he⟩ := f.property.1 ⟨x, trivial⟩ hx
    have hne : ∀ᶠ y in 𝓝 x, y ≠ p :=
      isOpen_compl_singleton.mem_nhds (by simpa using hx)
    have hlocal : F =ᶠ[𝓝 x] fun y => b ((chartAt ℂ x) y) := by
      filter_upwards [he, hne] with y hey hyp
      simpa [F, hyp] using hey trivial hyp
    exact ⟨b, hb, hlocal, hlocal.self_of_nhds⟩
  have ha : AnalyticAt ℂ a z₀ := (Classical.choose_spec (f.property.2 trivial)).1
  let b : ℂ → ℂ := fun z => a z / (z - z₀)
  have hb : MeromorphicAt b z₀ :=
    ha.meromorphicAt.div ((analyticAt_id.sub analyticAt_const).meromorphicAt)
  have hlocalp : F =ᶠ[𝓝[≠] p] fun y => b ((chartAt ℂ p) y) := by
    have hne : ∀ᶠ y in 𝓝[≠] p, (chartAt ℂ p) y ≠ z₀ :=
      (chartAt ℂ p).eventually_ne_nhdsWithin (mem_chart_source ℂ p)
    filter_upwards [(Classical.choose_spec (f.property.2 trivial)).2, hne]
      with y he hcy
    have hyp : y ≠ p := by
      intro h
      exact hcy (by simpa [h, z₀])
    have hmul := he trivial hyp
    dsimp [F, b]
    rw [dif_neg hyp]
    apply (eq_div_iff (sub_ne_zero.mpr hcy)).2
    change ((chartAt ℂ p) y - z₀) * _ = a ((chartAt ℂ p) y) at hmul
    simpa only [mul_comm] using hmul
  have horder : meromorphicOrderAt b z₀ = (-1 : ℤ) := by
    apply (meromorphicOrderAt_eq_int_iff hb).2
    refine ⟨a, ha, hf, ?_⟩
    have hne : ∀ᶠ z in 𝓝[≠] z₀, z ≠ z₀ := self_mem_nhdsWithin
    filter_upwards [hne] with z hz
    simp [b, zpow_neg_one, smul_eq_mul, div_eq_mul_inv, mul_comm]
  let G : SurfaceMeromorphicFunction E :=
    ⟨F, by
      intro x
      by_cases hx : x = p
      · subst x
        exact ⟨b, hb, hlocalp⟩
      · obtain ⟨c, hc, hlocal, _⟩ := hreg x hx
        exact ⟨c, hc.meromorphicAt,
          hlocal.filter_mono nhdsWithin_le_nhds⟩⟩
  refine ⟨G, ?_, hreg⟩
  exact (actualDivisorOrder_eq_chart_order G p b hlocalp).trans horder

theorem actualGenusTwo_globalPole_coefficient_zero
    (E : Type) [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (hg : CurveComplex.IsGenus E 2) (A : ChartedSpace ℂ E)
    (hA : letI : ChartedSpace ℂ E := A; IsManifold 𝓘(ℂ) ∞ E) :
    letI : ChartedSpace ℂ E := A
    letI : IsManifold 𝓘(ℂ) ∞ E := hA
    ∀ (p : E) (f : PoleOneOn p ⊤), coeffAt p ⊤ trivial f = 0 := by
  letI : ChartedSpace ℂ E := A
  letI : IsManifold 𝓘(ℂ) ∞ E := hA
  intro p f
  by_contra hf
  obtain ⟨F, hpole, hreg⟩ := actualGlobalPole_nonzero_coefficient_gives_simple_pole p f hf
  exact SurfaceMeromorphicFunction.genus_two_no_simple_pole
    E hg A F p hpole hreg

theorem actualGenusTwo_scalarCechBoundary_zero_iff
    (E : Type) [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (hg : CurveComplex.IsGenus E 2) (A : ChartedSpace ℂ E)
    (hA : letI : ChartedSpace ℂ E := A; IsManifold 𝓘(ℂ) ∞ E) :
    letI : ChartedSpace ℂ E := A
    letI : IsManifold 𝓘(ℂ) ∞ E := hA
    ∀ (p : E) (c : ℂ), scalarCechBoundary p c = 0 ↔ c = 0 := by
  letI : ChartedSpace ℂ E := A
  letI : IsManifold 𝓘(ℂ) ∞ E := hA
  intro p c
  constructor
  · intro hc
    obtain ⟨g, h, he⟩ := localPoleCechBoundary_zero_gives_global_correction p
      (chartSourceOpen p) (mem_chart_source ℂ p) (chartPoleSection p c) hc
    have heq := congrArg (coeffAt p (chartSourceOpen p) (mem_chart_source ℂ p)) he
    rw [coeffAt_global_restrict, map_sub, coeffAt_chartPoleSection,
      coeffAt_holToPole_zero, sub_zero] at heq
    exact heq.symm.trans (actualGenusTwo_globalPole_coefficient_zero E hg A hA p g)
  · intro hc
    simp [hc]

theorem actualGenusTwo_scalarCechBoundary_injective
    (E : Type) [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (hg : CurveComplex.IsGenus E 2) (A : ChartedSpace ℂ E)
    (hA : letI : ChartedSpace ℂ E := A; IsManifold 𝓘(ℂ) ∞ E) :
    letI : ChartedSpace ℂ E := A
    letI : IsManifold 𝓘(ℂ) ∞ E := hA
    ∀ p : E, Function.Injective (scalarCechBoundary p) := by
  letI : ChartedSpace ℂ E := A
  letI : IsManifold 𝓘(ℂ) ∞ E := hA
  intro p
  exact (injective_iff_map_eq_zero (scalarCechBoundary p)).mpr
    (fun c hc => (actualGenusTwo_scalarCechBoundary_zero_iff E hg A hA p c).mp hc)

#print axioms actualGenusTwo_scalarCechBoundary_injective
end CanonicalDimensionTwo
