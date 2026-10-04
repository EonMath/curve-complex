import CurveComplexGenusTwo.Topology.ActualIntervalLocalComparison.IntervalLocalNeighborhood

open scoped Manifold ContDiff Bundle Simplicial
open CanonicalDimensionTwo

namespace CanonicalDimensionTwo

noncomputable def actualChartRootArc {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (z : Metric.ball c r) (x : ActualChartBall E q c r) : ActualRegularPath E :=
  actualChartBallRegularArc q c r htarget z ⟨(chartAt ℂ q) x.1, x.2.2⟩

theorem actualChartRootArc_zero {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (z : Metric.ball c r) (x : ActualChartBall E q c r) :
    (actualChartRootArc q c r htarget z x).toFun 0 =
      (chartAt ℂ q).symm z := by
  exact actualChartSmoothArc_zero q c r htarget z _

theorem actualChartRootArc_one {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (z : Metric.ball c r) (x : ActualChartBall E q c r) :
    (actualChartRootArc q c r htarget z x).toFun 1 = x.1 := by
  change actualChartSmoothArc q c r htarget z
    ⟨(chartAt ℂ q) x.1, x.2.2⟩ 1 = x.1
  rw [actualChartSmoothArc_one]
  exact (chartAt ℂ q).left_inv x.2.1

theorem actualChartRootArc_source {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (z : Metric.ball c r) (x : ActualChartBall E q c r) (t : ℝ) :
    (actualChartRootArc q c r htarget z x).toFun t ∈
      (chartAt ℂ q).source :=
  actualChartSmoothArc_source q c r htarget z _ t

theorem actualChartRootArc_ball {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (z : Metric.ball c r) (x : ActualChartBall E q c r) (t : ℝ) :
    (chartAt ℂ q) ((actualChartRootArc q c r htarget z x).toFun t) ∈
      Metric.ball c r :=
  actualChartSmoothArc_chart_ball q c r htarget z _ t

noncomputable def actualChartRootEdgeTriangle {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (z : Metric.ball c r) (γ : ActualRegularPath E)
    (hs : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ.toFun t ∈ (chartAt ℂ q).source)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (chartAt ℂ q) (γ.toFun t) ∈ Metric.ball c r) :
    IntervalLocalRegularChartTriangle E where
  edge01 := actualChartRootArc q c r htarget z
    ⟨γ.toFun 0, hs 0 (by norm_num), hb 0 (by norm_num)⟩
  edge12 := γ
  edge20 := (actualChartRootArc q c r htarget z
    ⟨γ.toFun 1, hs 1 (by norm_num), hb 1 (by norm_num)⟩).reverse
  chartCenter := q
  ballCenter := c
  radius := r
  edge_source := by
    intro η hη t ht
    rcases hη with h | h | h
    · subst η
      exact actualChartRootArc_source q c r htarget z _ t
    · subst η
      exact hs t ht
    · subst η
      exact actualChartRootArc_source q c r htarget z _ (1 - t)
  edge_ball := by
    intro η hη t ht
    rcases hη with h | h | h
    · subst η
      exact actualChartRootArc_ball q c r htarget z _ t
    · subst η
      exact hb t ht
    · subst η
      exact actualChartRootArc_ball q c r htarget z _ (1 - t)
  ball_target := htarget
  endpoint01 := by
    exact actualChartRootArc_one q c r htarget z _
  endpoint12 := by
    change γ.toFun 1 =
      (actualChartRootArc q c r htarget z
        ⟨γ.toFun 1, hs 1 (by norm_num), hb 1 (by norm_num)⟩).toFun (1 - 0)
    simpa only [sub_zero] using (actualChartRootArc_one q c r htarget z
      ⟨γ.toFun 1, hs 1 (by norm_num), hb 1 (by norm_num)⟩).symm
  endpoint20 := by
    change (actualChartRootArc q c r htarget z _).toFun (1 - 1) =
      (actualChartRootArc q c r htarget z _).toFun 0
    simp only [sub_self]
    rw [actualChartRootArc_zero, actualChartRootArc_zero]

theorem actualChartRootEdge_deviation_mem {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (z : Metric.ball c r) (γ : ActualRegularPath E)
    (hs : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ.toFun t ∈ (chartAt ℂ q).source)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (chartAt ℂ q) (γ.toFun t) ∈ Metric.ball c r) :
    intervalLocalRegularTwoBoundaryToCycles
        (Finsupp.single
          (actualChartRootEdgeTriangle q c r htarget z γ hs hb) 1) -
      actualRegularReverseCycle (actualChartRootArc q c r htarget z
        ⟨γ.toFun 1, hs 1 (by norm_num), hb 1 (by norm_num)⟩) ∈
      intervalLocalNormalizedRelations (E := E) := by
  have htriangle : intervalLocalRegularTwoBoundaryToCycles
      (Finsupp.single
        (actualChartRootEdgeTriangle q c r htarget z γ hs hb) 1) ∈
      intervalLocalNormalizedRelations (E := E) :=
    Submodule.subset_span (Or.inl (Or.inl (Or.inl ⟨_, rfl⟩)))
  have hreverse : actualRegularReverseCycle (actualChartRootArc q c r htarget z
        ⟨γ.toFun 1, hs 1 (by norm_num), hb 1 (by norm_num)⟩) ∈
      intervalLocalNormalizedRelations (E := E) :=
    Submodule.subset_span (Or.inl (Or.inr ⟨_, rfl⟩))
  exact (intervalLocalNormalizedRelations (E := E)).sub_mem htriangle hreverse

theorem actualChartRootEdge_deviation_chain {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (z : Metric.ball c r) (γ : ActualRegularPath E)
    (hs : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ.toFun t ∈ (chartAt ℂ q).source)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (chartAt ℂ q) (γ.toFun t) ∈ Metric.ball c r) :
    (intervalLocalRegularTwoBoundaryToCycles
        (Finsupp.single
          (actualChartRootEdgeTriangle q c r htarget z γ hs hb) 1) -
      actualRegularReverseCycle (actualChartRootArc q c r htarget z
        ⟨γ.toFun 1, hs 1 (by norm_num), hb 1 (by norm_num)⟩)).1 =
      Finsupp.single γ 1 +
        Finsupp.single (actualChartRootArc q c r htarget z
          ⟨γ.toFun 0, hs 0 (by norm_num), hb 0 (by norm_num)⟩) 1 -
        Finsupp.single (actualChartRootArc q c r htarget z
          ⟨γ.toFun 1, hs 1 (by norm_num), hb 1 (by norm_num)⟩) 1 := by
  simp [intervalLocalRegularTwoBoundaryToCycles, intervalLocalRegularTwoBoundary,
    actualChartRootEdgeTriangle, actualRegularReverseCycle]
  abel

noncomputable def actualChartRootPathAtPoint {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (z : Metric.ball c r) (x : E) : ActualRegularPath E := by
  classical
  exact if hx : x ∈ actualChartBallOpenSet q c r then
    actualChartRootArc q c r htarget z ⟨x, hx⟩
  else ActualRegularPath.const ((chartAt ℂ q).symm z)

theorem actualChartRootPathAtPoint_of_mem {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (z : Metric.ball c r) (x : E)
    (hx : x ∈ actualChartBallOpenSet q c r) :
    actualChartRootPathAtPoint q c r htarget z x =
      actualChartRootArc q c r htarget z ⟨x, hx⟩ := by
  simp [actualChartRootPathAtPoint, hx]

theorem actualChartRootPathAtPoint_zero {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (z : Metric.ball c r) (x : E) :
    (actualChartRootPathAtPoint q c r htarget z x).toFun 0 =
      (chartAt ℂ q).symm z := by
  by_cases hx : x ∈ actualChartBallOpenSet q c r
  · rw [actualChartRootPathAtPoint_of_mem q c r htarget z x hx,
      actualChartRootArc_zero]
  · simp [actualChartRootPathAtPoint, hx, ActualRegularPath.const]

theorem actualChartRootPathAtPoint_one_of_mem {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (z : Metric.ball c r) (x : E)
    (hx : x ∈ actualChartBallOpenSet q c r) :
    (actualChartRootPathAtPoint q c r htarget z x).toFun 1 = x := by
  rw [actualChartRootPathAtPoint_of_mem q c r htarget z x hx,
    actualChartRootArc_one]

noncomputable def actualChartRootOnPoints {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (z : Metric.ball c r) : (E →₀ ℤ) →ₗ[ℤ] ActualRegularOneChains E :=
  Finsupp.linearCombination ℤ (fun x : E =>
    Finsupp.single (actualChartRootPathAtPoint q c r htarget z x) 1)

noncomputable def actualChartRootDeviationCycle {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (z : Metric.ball c r) (γ : ActualRegularPath E)
    (hs : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ.toFun t ∈ (chartAt ℂ q).source)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (chartAt ℂ q) (γ.toFun t) ∈ Metric.ball c r) :
    ActualRegularOneCycles E :=
  intervalLocalRegularTwoBoundaryToCycles
      (Finsupp.single (actualChartRootEdgeTriangle q c r htarget z γ hs hb) 1) -
    actualRegularReverseCycle (actualChartRootArc q c r htarget z
      ⟨γ.toFun 1, hs 1 (by norm_num), hb 1 (by norm_num)⟩)

theorem actualChartRootDeviationCycle_mem {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (z : Metric.ball c r) (γ : ActualRegularPath E)
    (hs : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ.toFun t ∈ (chartAt ℂ q).source)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (chartAt ℂ q) (γ.toFun t) ∈ Metric.ball c r) :
    actualChartRootDeviationCycle q c r htarget z γ hs hb ∈
      intervalLocalNormalizedRelations (E := E) :=
  actualChartRootEdge_deviation_mem q c r htarget z γ hs hb

theorem actualChartRootDeviationCycle_chain {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (z : Metric.ball c r) (γ : ActualRegularPath E)
    (hs : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ.toFun t ∈ (chartAt ℂ q).source)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (chartAt ℂ q) (γ.toFun t) ∈ Metric.ball c r) :
    (actualChartRootDeviationCycle q c r htarget z γ hs hb).1 =
      Finsupp.single γ 1 -
        actualChartRootOnPoints q c r htarget z
          (actualRegularChainBoundary (Finsupp.single γ 1)) := by
  change (intervalLocalRegularTwoBoundaryToCycles
        (Finsupp.single (actualChartRootEdgeTriangle q c r htarget z γ hs hb) 1) -
      actualRegularReverseCycle (actualChartRootArc q c r htarget z
        ⟨γ.toFun 1, hs 1 (by norm_num), hb 1 (by norm_num)⟩)).1 = _
  rw [actualChartRootEdge_deviation_chain]
  rw [actualRegularChainBoundary_single, map_sub]
  simp only [actualChartRootOnPoints, Finsupp.linearCombination_single, one_smul]
  rw [actualChartRootPathAtPoint_of_mem q c r htarget z (γ.toFun 1)
    ⟨hs 1 (by norm_num), hb 1 (by norm_num)⟩,
    actualChartRootPathAtPoint_of_mem q c r htarget z (γ.toFun 0)
    ⟨hs 0 (by norm_num), hb 0 (by norm_num)⟩]
  abel

theorem actualChartBallRegularCycle_mem_relations {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (z : Metric.ball c r) (a : ActualRegularOneCycles E)
    (hs : ∀ γ ∈ a.1.support, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ.toFun t ∈ (chartAt ℂ q).source)
    (hb : ∀ γ ∈ a.1.support, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (chartAt ℂ q) (γ.toFun t) ∈ Metric.ball c r) :
    a ∈ intervalLocalNormalizedRelations (E := E) := by
  let w : ActualRegularOneCycles E :=
    ∑ γ ∈ a.1.support.attach,
      (a.1 γ.1) • actualChartRootDeviationCycle q c r htarget z γ.1
        (hs γ.1 γ.2) (hb γ.1 γ.2)
  have hw : w ∈ intervalLocalNormalizedRelations (E := E) := by
    dsimp [w]
    apply Submodule.sum_mem
    intro γ hγ
    exact (intervalLocalNormalizedRelations (E := E)).smul_mem _
      (actualChartRootDeviationCycle_mem q c r htarget z γ.1
        (hs γ.1 γ.2) (hb γ.1 γ.2))
  have heq : w.1 = a.1 -
      actualChartRootOnPoints q c r htarget z (actualRegularChainBoundary a.1) := by
    have ha : a.1 = ∑ γ ∈ a.1.support, Finsupp.single γ (a.1 γ) := by
      simpa [Finsupp.sum] using (Finsupp.sum_single a.1).symm
    rw [← Finset.sum_attach] at ha
    rw [ha]
    simp only [w, Submodule.coe_sum, Submodule.coe_smul, map_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro γ hγ
    have hsingle : Finsupp.single γ.1 (a.1 γ.1) =
        (a.1 γ.1) • (Finsupp.single γ.1 1 : ActualRegularOneChains E) := by simp
    rw [hsingle, map_smul, map_smul]
    rw [actualChartRootDeviationCycle_chain q c r htarget z γ.1
      (hs γ.1 γ.2) (hb γ.1 γ.2)]
    simp only [smul_sub]
  have hzero : actualRegularChainBoundary a.1 = 0 := a.2
  have hwa : w = a := by
    apply Subtype.ext
    simpa [hzero] using heq
  rwa [← hwa]

end CanonicalDimensionTwo
