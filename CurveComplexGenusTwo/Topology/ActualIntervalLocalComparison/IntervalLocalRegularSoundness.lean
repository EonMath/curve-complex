import CurveComplexGenusTwo.Topology.ActualIntervalLocalComparison.IntervalLocalRegularHOne

open scoped Manifold ContDiff Bundle Simplicial
open Convexity CategoryTheory CurveComplexGenusTwo.CWHurewicz
open CanonicalDimensionTwo

namespace CanonicalDimensionTwo

theorem intervalLocalRegularPathIntegral_primitive_sub {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (γ : ActualRegularPath E)
    (q : E) (c : ℂ) (r : ℝ) (F : ℂ → ℂ)
    (hq : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ.toFun t ∈ (chartAt ℂ q).source)
    (hball : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (chartAt ℂ q) (γ.toFun t) ∈ Metric.ball c r)
    (hF : ∀ z ∈ Metric.ball c r,
      HasDerivWithinAt F
        (actualLocalOneForm s q z (fun _ : Fin 1 => (1 : ℂ)))
        (Metric.ball c r) z) :
    actualPathIntegral s γ.toFun =
      F ((chartAt ℂ q) (γ.toFun 1)) - F ((chartAt ℂ q) (γ.toFun 0)) := by
  let z : ℝ → ℂ := fun t => (chartAt ℂ q) (γ.toFun t)
  have hderiv (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : HasDerivAt (F ∘ z)
      (actualPathIntegrand s γ.toFun t) t := by
    have hz : HasDerivAt z ((fderiv ℝ z t) 1) t :=
      (actualPathDifferentiable_fixed_chart γ.toFun t q
        γ.continuous.continuousAt (γ.chartDifferentiable t) (hq t ht)).hasFDerivAt.hasDerivAt
    have hFa : HasDerivAt F
        (actualLocalOneForm s q (z t) (fun _ : Fin 1 => (1 : ℂ))) (z t) :=
      (hF (z t) (hball t ht)).hasDerivAt
        (Metric.isOpen_ball.mem_nhds (hball t ht))
    have hcomp := (hFa.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hz
    convert hcomp using 1
    rw [actualPathIntegrand_fixed_chart s γ.toFun t q
      γ.continuous.continuousAt (γ.chartDifferentiable t) (hq t ht),
      actualLocalOneForm_apply_eq_mul_coefficient]
    simp [z, ContinuousLinearMap.toSpanSingleton_apply]
  have hint : IntervalIntegrable (deriv (F ∘ z)) MeasureTheory.volume 0 1 := by
    apply (γ.integrable s).congr
    intro t ht
    rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at ht
    exact (hderiv t ⟨le_of_lt ht.1, ht.2⟩).deriv.symm
  calc
    actualPathIntegral s γ.toFun = ∫ t in (0 : ℝ)..1, deriv (F ∘ z) t := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact (hderiv t (by simpa only [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht)).deriv.symm
    _ = F (z 1) - F (z 0) := intervalIntegral.integral_deriv_eq_sub
      (fun t ht => (hderiv t (by simpa only [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht)).differentiableAt) hint

theorem intervalLocalRegularTriangleBoundary_integral_zero {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (Δ : IntervalLocalRegularChartTriangle E) :
    actualPathIntegral s Δ.edge01.toFun +
      actualPathIntegral s Δ.edge12.toFun +
      actualPathIntegral s Δ.edge20.toFun = 0 := by
  obtain ⟨F, hF⟩ := actualLocalOneForm_has_primitive_on_ball
    s Δ.chartCenter Δ.ballCenter Δ.radius Δ.ball_target
  rw [intervalLocalRegularPathIntegral_primitive_sub s Δ.edge01
    Δ.chartCenter Δ.ballCenter Δ.radius F
    (Δ.edge_source Δ.edge01 (by simp)) (Δ.edge_ball Δ.edge01 (by simp)) hF,
    intervalLocalRegularPathIntegral_primitive_sub s Δ.edge12
    Δ.chartCenter Δ.ballCenter Δ.radius F
    (Δ.edge_source Δ.edge12 (by simp)) (Δ.edge_ball Δ.edge12 (by simp)) hF,
    intervalLocalRegularPathIntegral_primitive_sub s Δ.edge20
    Δ.chartCenter Δ.ballCenter Δ.radius F
    (Δ.edge_source Δ.edge20 (by simp)) (Δ.edge_ball Δ.edge20 (by simp)) hF,
    Δ.endpoint01, Δ.endpoint12, Δ.endpoint20]
  abel

theorem intervalLocalRegularTwoBoundary_period_zero {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) :
    (actualRegularChainIntegral s).comp intervalLocalRegularTwoBoundary = 0 := by
  apply Finsupp.lhom_ext
  intro Δ n
  simp only [LinearMap.comp_apply, LinearMap.zero_apply,
    intervalLocalRegularTwoBoundary, Finsupp.linearCombination_single,
    map_smul]
  have hΔ := intervalLocalRegularTriangleBoundary_integral_zero s Δ
  simp only [actualRegularChainIntegral, map_add, Finsupp.linearCombination_single,
    one_smul]
  linear_combination (n : ℂ) * hΔ

noncomputable def intervalLocalChartBallEdge {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ) (γ : ActualRegularPath E)
    (hs : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ.toFun t ∈ (chartAt ℂ q).source)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (chartAt ℂ q) (γ.toFun t) ∈ Metric.ball c r) :
    (TopCat.toSSet.obj (TopCat.of (ActualChartBall E q c r))) _⦋1⦌ :=
  (TopCat.toSSetObjEquiv (TopCat.of (ActualChartBall E q c r)) (.op ⦋1⦌)).symm
    ⟨fun u => ⟨γ.toFun ((TopCat.stdSimplexHomeomorphI.{0} u).down : ℝ),
      hs _ (TopCat.stdSimplexHomeomorphI.{0} u).down.2,
      hb _ (TopCat.stdSimplexHomeomorphI.{0} u).down.2⟩, by
      apply Continuous.subtype_mk
      exact γ.continuous.comp (by fun_prop)⟩

theorem intervalLocalChartBallEdge_face_zero {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ) (γ : ActualRegularPath E)
    (hs : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ.toFun t ∈ (chartAt ℂ q).source)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (chartAt ℂ q) (γ.toFun t) ∈ Metric.ball c r) :
    (TopCat.toSSet.obj (TopCat.of (ActualChartBall E q c r))).δ (0 : Fin 2)
      (intervalLocalChartBallEdge q c r γ hs hb) =
      TopCat.toSSetObj₀Equiv.symm
        (⟨γ.toFun 1, hs 1 (by norm_num), hb 1 (by norm_num)⟩ :
          ActualChartBall E q c r) := by
  apply TopCat.toSSetObj₀Equiv.injective
  change (TopCat.toSSetObjEquiv (TopCat.of (ActualChartBall E q c r)) (.op ⦋0⦌))
    ((TopCat.toSSet.obj (TopCat.of (ActualChartBall E q c r))).δ (0 : Fin 2)
      (intervalLocalChartBallEdge q c r γ hs hb)) default = _
  rw [TopCat.toSSetObjEquiv_δ_apply]
  rw [Subsingleton.elim (default : StdSimplex ℝ (Fin 1)) (StdSimplex.single 0),
    StdSimplex.map_single]
  apply Subtype.ext
  simp [intervalLocalChartBallEdge]
  rfl

theorem intervalLocalChartBallEdge_face_one {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ) (γ : ActualRegularPath E)
    (hs : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ.toFun t ∈ (chartAt ℂ q).source)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (chartAt ℂ q) (γ.toFun t) ∈ Metric.ball c r) :
    (TopCat.toSSet.obj (TopCat.of (ActualChartBall E q c r))).δ (1 : Fin 2)
      (intervalLocalChartBallEdge q c r γ hs hb) =
      TopCat.toSSetObj₀Equiv.symm
        (⟨γ.toFun 0, hs 0 (by norm_num), hb 0 (by norm_num)⟩ :
          ActualChartBall E q c r) := by
  apply TopCat.toSSetObj₀Equiv.injective
  change (TopCat.toSSetObjEquiv (TopCat.of (ActualChartBall E q c r)) (.op ⦋0⦌))
    ((TopCat.toSSet.obj (TopCat.of (ActualChartBall E q c r))).δ (1 : Fin 2)
      (intervalLocalChartBallEdge q c r γ hs hb)) default = _
  rw [TopCat.toSSetObjEquiv_δ_apply]
  rw [Subsingleton.elim (default : StdSimplex ℝ (Fin 1)) (StdSimplex.single 0),
    StdSimplex.map_single]
  apply Subtype.ext
  simp [intervalLocalChartBallEdge]
  rfl

theorem intervalLocalChartBallEdge_boundary {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ) (γ : ActualRegularPath E)
    (hs : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ.toFun t ∈ (chartAt ℂ q).source)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (chartAt ℂ q) (γ.toFun t) ∈ Metric.ball c r) :
    singularBoundaryFinsupp (TopCat.of (ActualChartBall E q c r)) 0
      (Finsupp.single (intervalLocalChartBallEdge q c r γ hs hb) 1) =
      Finsupp.single (TopCat.toSSetObj₀Equiv.symm
        (⟨γ.toFun 1, hs 1 (by norm_num), hb 1 (by norm_num)⟩ :
          ActualChartBall E q c r)) 1 -
      Finsupp.single (TopCat.toSSetObj₀Equiv.symm
        (⟨γ.toFun 0, hs 0 (by norm_num), hb 0 (by norm_num)⟩ :
          ActualChartBall E q c r)) 1 := by
  rw [singularBoundaryFinsupp_single]
  simp [Fin.sum_univ_two, intervalLocalChartBallEdge_face_zero,
    intervalLocalChartBallEdge_face_one, sub_eq_add_neg]

theorem intervalLocalChartBallEdge_push {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ) (γ : ActualRegularPath E)
    (hs : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ.toFun t ∈ (chartAt ℂ q).source)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (chartAt ℂ q) (γ.toFun t) ∈ Metric.ball c r) :
    (TopCat.toSSet.map (actualChartBallInclusion q c r)).app (.op ⦋1⦌)
      (intervalLocalChartBallEdge q c r γ hs hb) = actualRegularPathAsSingular γ := by
  apply (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌)).injective
  apply ContinuousMap.ext
  intro u
  rfl

noncomputable def intervalLocalChartTriangleBallCycle {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (Δ : IntervalLocalRegularChartTriangle E) :
    (TopCat.toSSet.obj (TopCat.of
      (ActualChartBall E Δ.chartCenter Δ.ballCenter Δ.radius))) _⦋1⦌ →₀ ℤ :=
  let hs (γ : ActualRegularPath E)
      (hγ : γ ∈ ({Δ.edge01, Δ.edge12, Δ.edge20} : Set (ActualRegularPath E))) :=
    Δ.edge_source γ hγ
  let hb (γ : ActualRegularPath E)
      (hγ : γ ∈ ({Δ.edge01, Δ.edge12, Δ.edge20} : Set (ActualRegularPath E))) :=
    Δ.edge_ball γ hγ
  Finsupp.single (intervalLocalChartBallEdge Δ.chartCenter Δ.ballCenter Δ.radius
      Δ.edge01 (hs Δ.edge01 (by simp)) (hb Δ.edge01 (by simp))) 1 +
    Finsupp.single (intervalLocalChartBallEdge Δ.chartCenter Δ.ballCenter Δ.radius
      Δ.edge12 (hs Δ.edge12 (by simp)) (hb Δ.edge12 (by simp))) 1 +
    Finsupp.single (intervalLocalChartBallEdge Δ.chartCenter Δ.ballCenter Δ.radius
      Δ.edge20 (hs Δ.edge20 (by simp)) (hb Δ.edge20 (by simp))) 1

theorem intervalLocalChartTriangleBallCycle_closed {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (Δ : IntervalLocalRegularChartTriangle E) :
    singularBoundaryFinsupp (TopCat.of
      (ActualChartBall E Δ.chartCenter Δ.ballCenter Δ.radius)) 0
      (intervalLocalChartTriangleBallCycle Δ) = 0 := by
  unfold intervalLocalChartTriangleBallCycle
  simp only [map_add]
  rw [intervalLocalChartBallEdge_boundary, intervalLocalChartBallEdge_boundary,
    intervalLocalChartBallEdge_boundary]
  simp only [Δ.endpoint01, Δ.endpoint12, Δ.endpoint20]
  abel

theorem intervalLocalChartTriangleBallCycle_push {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (Δ : IntervalLocalRegularChartTriangle E) :
    singularFinsuppPush
      (actualChartBallInclusion Δ.chartCenter Δ.ballCenter Δ.radius) 1
      (intervalLocalChartTriangleBallCycle Δ) =
      actualRegularChainsToSingular
        (intervalLocalRegularTwoBoundary (Finsupp.single Δ 1)) := by
  unfold intervalLocalChartTriangleBallCycle
  simp only [map_add, intervalLocalRegularTwoBoundary,
    Finsupp.linearCombination_single, one_smul]
  simp [singularFinsuppPush, actualRegularChainsToSingular,
    intervalLocalChartBallEdge_push, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single]

theorem intervalLocalChartTriangle_singular_fill {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (Δ : IntervalLocalRegularChartTriangle E) :
    ∃ b : (TopCat.toSSet.obj (TopCat.of E)) _⦋2⦌ →₀ ℤ,
      singularBoundaryFinsupp (TopCat.of E) 1 b =
        actualRegularChainsToSingular
          (intervalLocalRegularTwoBoundary (Finsupp.single Δ 1)) := by
  let X := ActualChartBall E Δ.chartCenter Δ.ballCenter Δ.radius
  have hne : (Metric.ball Δ.ballCenter Δ.radius).Nonempty :=
    ⟨(chartAt ℂ Δ.chartCenter) (Δ.edge01.toFun 0),
      Δ.edge_ball Δ.edge01 (by simp) 0 (by norm_num)⟩
  letI : ContractibleSpace X :=
    actualChartBall_contractible Δ.chartCenter Δ.ballCenter Δ.radius
      Δ.ball_target hne
  obtain ⟨b, hb⟩ := actualSingularCycle_fill_contractible X
    (intervalLocalChartTriangleBallCycle Δ) (intervalLocalChartTriangleBallCycle_closed Δ)
  refine ⟨singularFinsuppPush
    (actualChartBallInclusion Δ.chartCenter Δ.ballCenter Δ.radius) 2 b, ?_⟩
  rw [singularFinsuppPush_boundary, hb, intervalLocalChartTriangleBallCycle_push]

noncomputable def intervalLocalChartTriangleSingularFill {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (Δ : IntervalLocalRegularChartTriangle E) :
    (TopCat.toSSet.obj (TopCat.of E)) _⦋2⦌ →₀ ℤ :=
  Classical.choose (intervalLocalChartTriangle_singular_fill Δ)

theorem intervalLocalChartTriangleSingularFill_boundary {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (Δ : IntervalLocalRegularChartTriangle E) :
    singularBoundaryFinsupp (TopCat.of E) 1
      (intervalLocalChartTriangleSingularFill Δ) =
        actualRegularChainsToSingular
          (intervalLocalRegularTwoBoundary (Finsupp.single Δ 1)) :=
  Classical.choose_spec (intervalLocalChartTriangle_singular_fill Δ)

noncomputable def intervalLocalTwoChainsToSingular {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    IntervalLocalRegularTwoChains E →ₗ[ℤ]
      ((TopCat.toSSet.obj (TopCat.of E)) _⦋2⦌ →₀ ℤ) :=
  Finsupp.linearCombination ℤ (intervalLocalChartTriangleSingularFill (E := E))

theorem intervalLocalTwoChainsToSingular_boundary {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    (singularBoundaryFinsupp (TopCat.of E) 1).comp
        (intervalLocalTwoChainsToSingular (E := E)) =
      (actualRegularChainsToSingular (E := E)).comp
        intervalLocalRegularTwoBoundary := by
  apply Finsupp.lhom_ext
  intro Δ n
  simp only [LinearMap.comp_apply, intervalLocalTwoChainsToSingular,
    Finsupp.linearCombination_single, map_smul]
  rw [intervalLocalChartTriangleSingularFill_boundary]
  simp [intervalLocalRegularTwoBoundary, actualRegularChainsToSingular,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    Finsupp.mapDomain_add, smul_add]

theorem intervalLocalRegularCyclesToSingular_triangle_boundary {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    (intervalLocalRegularTwoBoundaryToCycles (E := E)).range ≤
      (actualSingularTwoBoundaries E).comap
        (actualRegularCyclesToSingular (E := E)) := by
  intro z hz
  obtain ⟨c, rfl⟩ := hz
  change actualRegularCyclesToSingular
    (intervalLocalRegularTwoBoundaryToCycles c) ∈ actualSingularTwoBoundaries E
  refine ⟨intervalLocalTwoChainsToSingular c, ?_⟩
  apply Subtype.ext
  change singularBoundaryFinsupp (TopCat.of E) 1
      (intervalLocalTwoChainsToSingular c) =
    actualRegularChainsToSingular (intervalLocalRegularTwoBoundary c)
  exact LinearMap.congr_fun
    (intervalLocalTwoChainsToSingular_boundary (E := E)) c

theorem intervalLocalNormalizedRelationSet_period_zero {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (z : ActualRegularOneCycles E)
    (hz : z ∈ intervalLocalNormalizedRelationSet (E := E)) :
    actualRegularCyclePeriod s z = 0 := by
  simp only [intervalLocalNormalizedRelationSet, Set.mem_union] at hz
  rcases hz with (((h | h) | h) | h)
  · obtain ⟨c, rfl⟩ := h
    have hc := LinearMap.congr_fun
      (intervalLocalRegularTwoBoundary_period_zero s) c
    simpa [actualRegularCyclePeriod, intervalLocalRegularTwoBoundaryToCycles] using hc
  · obtain ⟨x, rfl⟩ := h
    exact actualRegularConstantCycle_period_zero s x
  · obtain ⟨γ, rfl⟩ := h
    exact actualRegularChainIntegral_reverse s γ
  · obtain ⟨γ, rfl⟩ := h
    exact actualRegularSubdivision_period_zero s γ

theorem intervalLocalNormalizedRelations_period_zero {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) :
    intervalLocalNormalizedRelations (E := E) ≤
      (actualRegularCyclePeriod s).ker := by
  apply Submodule.span_le.mpr
  intro z hz
  exact intervalLocalNormalizedRelationSet_period_zero s z hz

theorem intervalLocalNormalizedRelationSet_singular_boundary {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (z : ActualRegularOneCycles E)
    (hz : z ∈ intervalLocalNormalizedRelationSet (E := E)) :
    actualRegularCyclesToSingular z ∈ actualSingularTwoBoundaries E := by
  simp only [intervalLocalNormalizedRelationSet, Set.mem_union] at hz
  rcases hz with (((h | h) | h) | h)
  · exact intervalLocalRegularCyclesToSingular_triangle_boundary h
  · obtain ⟨x, rfl⟩ := h
    have hq := actualRegularConstantCycle_maps_zero x
    rw [actualRegularChartHomologyToSingular_mk] at hq
    exact (Submodule.Quotient.mk_eq_zero _).mp hq
  · obtain ⟨γ, rfl⟩ := h
    exact actualRegularReverseCycle_singular_boundary γ
  · obtain ⟨γ, rfl⟩ := h
    exact actualRegularSubdivisionCycle_singular_boundary γ

theorem intervalLocalNormalizedRelations_singular_boundary {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    intervalLocalNormalizedRelations (E := E) ≤
      (actualSingularTwoBoundaries E).comap
        (actualRegularCyclesToSingular (E := E)) := by
  apply Submodule.span_le.mpr
  intro z hz
  exact intervalLocalNormalizedRelationSet_singular_boundary z hz

noncomputable def intervalLocalNormalizedRegularPeriod {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) : IntervalLocalNormalizedRegularHOne E →ₗ[ℤ] ℂ :=
  (intervalLocalNormalizedRelations (E := E)).liftQ
    (actualRegularCyclePeriod s)
    (intervalLocalNormalizedRelations_period_zero s)

theorem intervalLocalNormalizedRegularPeriod_mk {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (z : ActualRegularOneCycles E) :
    intervalLocalNormalizedRegularPeriod s
      ((intervalLocalNormalizedRelations (E := E)).mkQ z) =
      actualRegularCyclePeriod s z := rfl

noncomputable def intervalLocalNormalizedRegularHOneToSingular {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    IntervalLocalNormalizedRegularHOne E →ₗ[ℤ] ActualSingularHOne E :=
  (intervalLocalNormalizedRelations (E := E)).liftQ
    ((actualSingularTwoBoundaries E).mkQ.comp
      (actualRegularCyclesToSingular (E := E))) (by
        intro z hz
        exact Submodule.Quotient.mk_eq_zero _ |>.mpr
          (intervalLocalNormalizedRelations_singular_boundary (E := E) hz))

theorem intervalLocalNormalizedRegularHOneToSingular_mk {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (z : ActualRegularOneCycles E) :
    intervalLocalNormalizedRegularHOneToSingular
      ((intervalLocalNormalizedRelations (E := E)).mkQ z) =
      (actualSingularTwoBoundaries E).mkQ
        (actualRegularCyclesToSingular z) := rfl

noncomputable def intervalLocalNormalizedRegularHOneToProject {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    IntervalLocalNormalizedRegularHOne E →ₗ[ℤ]
      CurveComplex.integralHomology E 1 :=
  (actualSingularHOneIsoProject E).hom.hom.comp
    (intervalLocalNormalizedRegularHOneToSingular (E := E))

theorem intervalLocalNormalizedRegularHOneToProject_mk {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (z : ActualRegularOneCycles E) :
    intervalLocalNormalizedRegularHOneToProject
      ((intervalLocalNormalizedRelations (E := E)).mkQ z) =
      (actualSingularHOneIsoProject E).hom.hom
        ((actualSingularTwoBoundaries E).mkQ
          (actualRegularCyclesToSingular z)) := by
  exact congrArg (actualSingularHOneIsoProject E).hom.hom
    (intervalLocalNormalizedRegularHOneToSingular_mk z)

theorem intervalLocalNormalizedRegularHOneToSingular_surjective {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    Function.Surjective (intervalLocalNormalizedRegularHOneToSingular (E := E)) := by
  intro z
  obtain ⟨c, rfl⟩ := (actualSingularTwoBoundaries E).mkQ_surjective z
  obtain ⟨a, b, hb⟩ :=
    actualSingularOneCycle_regularize_cycle c.1 c.2
  refine ⟨(intervalLocalNormalizedRelations (E := E)).mkQ a, ?_⟩
  rw [intervalLocalNormalizedRegularHOneToSingular_mk]
  apply Submodule.Quotient.eq _ |>.mpr
  change actualRegularCyclesToSingular a - c ∈ actualSingularTwoBoundaries E
  refine ⟨-b, ?_⟩
  apply Subtype.ext
  change singularBoundaryFinsupp (TopCat.of E) 1 (-b) =
    actualRegularChainsToSingular a.1 - c.1
  rw [map_neg, hb]
  abel

theorem intervalLocalNormalizedRegularHOneToProject_surjective {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    Function.Surjective (intervalLocalNormalizedRegularHOneToProject (E := E)) := by
  intro z
  let y := (actualSingularHOneIsoProject E).inv z
  have hy : (actualSingularHOneIsoProject E).hom y = z := by
    exact (actualSingularHOneIsoProject E).inv_hom_id_apply z
  rw [← hy]
  obtain ⟨x, hx⟩ := intervalLocalNormalizedRegularHOneToSingular_surjective y
  refine ⟨x, ?_⟩
  change (actualSingularHOneIsoProject E).hom
    (intervalLocalNormalizedRegularHOneToSingular x) = _
  rw [hx]

end CanonicalDimensionTwo
