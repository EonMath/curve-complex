import CurveComplexGenusTwo.Topology.ActualIntervalLocalComparison.IntervalLocalChartAcyclic

open scoped Manifold ContDiff Bundle Simplicial
open Convexity CategoryTheory CurveComplexGenusTwo.CWHurewicz
open CanonicalDimensionTwo

namespace CanonicalDimensionTwo

abbrev ActualChartBallIndexInside (E : Type) [TopologicalSpace E]
    [ChartedSpace ℂ E] (U : Set E) :=
  {i : ActualChartBallIndex E // actualChartBallCover i ⊆ U}

theorem actualChartBallIndexInside_covers {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E]
    (U : Set E) (hU : IsOpen U) (x : E) (hx : x ∈ U) :
    ∃ i : ActualChartBallIndexInside E U, x ∈ actualChartBallCover i.1 := by
  obtain ⟨r, _, htarget, hmem, hsubset⟩ :=
    actualChartBallOpenSet_refines_open U hU x hx
  exact ⟨⟨⟨x, (chartAt ℂ x) x, r, htarget⟩, hsubset⟩, hmem⟩

theorem actualSingularEdge_openChartBallLebesgue {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E]
    (U : Set E) (hU : IsOpen U)
    (σ : (TopCat.toSSet.obj (TopCat.of E)) _⦋1⦌)
    (hσ : ∀ u : StdSimplex ℝ (Fin 2),
      (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌) σ) u ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ u : StdSimplex ℝ (Fin 2),
        ∃ i : ActualChartBallIndexInside E U,
          ∀ v ∈ Metric.ball u δ,
            (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌) σ) v ∈
              actualChartBallCover i.1 := by
  let f := TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌) σ
  let V : ActualChartBallIndexInside E U → Set (StdSimplex ℝ (Fin 2)) :=
    fun i => f ⁻¹' actualChartBallCover i.1
  have hV : ∀ i, IsOpen (V i) := by
    intro i
    exact (actualChartBallCover_isOpen i.1).preimage f.continuous
  have hcover : (Set.univ : Set (StdSimplex ℝ (Fin 2))) ⊆ ⋃ i, V i := by
    intro u _
    obtain ⟨i, hi⟩ := actualChartBallIndexInside_covers U hU (f u) (hσ u)
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨δ, hδ, hballs⟩ :=
    lebesgue_number_lemma_of_metric isCompact_univ hV hcover
  refine ⟨δ, hδ, ?_⟩
  intro u
  obtain ⟨i, hi⟩ := hballs u (Set.mem_univ u)
  exact ⟨i, fun v hv => hi hv⟩

theorem actualSingularEdge_openChartBallSubdivision {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E]
    (U : Set E) (hU : IsOpen U)
    (σ : (TopCat.toSSet.obj (TopCat.of E)) _⦋1⦌)
    (hσ : ∀ u : StdSimplex ℝ (Fin 2),
      (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌) σ) u ∈ U) :
    ∃ k : ℕ,
      ∀ ss : List (Equiv.Perm (Fin 2)), ss.length = k →
        ∃ i : ActualChartBallIndexInside E U,
          ∀ u : StdSimplex ℝ (Fin 2),
            (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌) σ)
              (barycentricFlagIterate 1 ss u) ∈ actualChartBallCover i.1 := by
  obtain ⟨δ, hδ, hcover⟩ := actualSingularEdge_openChartBallLebesgue U hU σ hσ
  obtain ⟨k, hk⟩ := barycentricFlagIterate_eventually_small 1 δ hδ
  refine ⟨k, ?_⟩
  intro ss hss
  let t : StdSimplex ℝ (Fin 2) := .single 0
  obtain ⟨i, hi⟩ := hcover (barycentricFlagIterate 1 ss t)
  refine ⟨i, fun u => hi _ ?_⟩
  exact Metric.mem_ball.mpr (hk ss hss u t)

theorem actualSingularEdge_subdivided_openChartSmall {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E]
    (U : Set E) (hU : IsOpen U)
    (σ : (TopCat.toSSet.obj (TopCat.of E)) _⦋1⦌)
    (hσ : ∀ u : StdSimplex ℝ (Fin 2),
      (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌) σ) u ∈ U) :
    ∃ k : ℕ,
      ∀ y ∈ (singularBarycentricIterate (TopCat.of E) 1 k
          (Finsupp.single σ 1)).support,
        ∃ i : ActualChartBallIndexInside E U,
          ∀ u : StdSimplex ℝ (Fin 2),
            (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌) y) u ∈
              actualChartBallCover i.1 := by
  obtain ⟨k, hk⟩ := actualSingularEdge_openChartBallSubdivision U hU σ hσ
  refine ⟨k, ?_⟩
  intro y hy
  rw [← actualSingularBarycentricIterateList_eq_iterate] at hy
  obtain ⟨x, hx, ss, hlen, rfl⟩ :=
    singularBarycentricIterateList_support (TopCat.of E) 1 k
      (Finsupp.single σ 1) y hy
  have hxσ : x = σ := by
    simpa using hx
  subst x
  obtain ⟨i, hi⟩ := hk ss hlen
  refine ⟨i, ?_⟩
  intro u
  rw [singularFlagIterate_eval]
  exact hi u

theorem actualOpenChartSmallSingularChain_regularize {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (U : Set E)
    (d : (TopCat.toSSet.obj (TopCat.of E)) _⦋1⦌ →₀ ℤ)
    (hd : ∀ y ∈ d.support,
      ∃ i : ActualChartBallIndexInside E U,
        ∀ u : StdSimplex ℝ (Fin 2),
          (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌) y) u ∈
            actualChartBallCover i.1) :
    ∃ a : ActualRegularOneChains E,
      (∀ γ ∈ a.support, ∀ t : ℝ, γ.toFun t ∈ U) ∧
      ∃ b : (TopCat.toSSet.obj (TopCat.of E)) _⦋2⦌ →₀ ℤ,
        singularBoundaryFinsupp (TopCat.of E) 1 b =
          d - actualRegularChainsToSingular a := by
  classical
  have hlocal (y : (TopCat.toSSet.obj (TopCat.of E)) _⦋1⦌)
      (hy : y ∈ d.support) :
      ∃ a : ActualRegularPath E,
        (∀ t : ℝ, a.toFun t ∈ U) ∧
        ∃ b : (TopCat.toSSet.obj (TopCat.of E)) _⦋2⦌ →₀ ℤ,
          singularBoundaryFinsupp (TopCat.of E) 1 b =
            Finsupp.single y 1 - Finsupp.single (actualRegularPathAsSingular a) 1 := by
    obtain ⟨i, hi⟩ := hd y hy
    obtain ⟨a, _, _, has, hab, b, hb⟩ :=
      actualChartSmallSingularEdge_regularize i.1.q i.1.c i.1.r i.1.target y
        (fun u => (hi u).1) (fun u => (hi u).2)
    refine ⟨a, ?_, b, hb⟩
    intro t
    exact i.2 ⟨has t, hab t⟩
  choose a ha b hb using hlocal
  let A : ActualRegularOneChains E :=
    ∑ y ∈ d.support.attach, Finsupp.single (a y.1 y.2) (d y.1)
  let B : (TopCat.toSSet.obj (TopCat.of E)) _⦋2⦌ →₀ ℤ :=
    ∑ y ∈ d.support.attach, (d y.1) • b y.1 y.2
  refine ⟨A, ?_, B, ?_⟩
  · intro γ hγ t
    obtain ⟨y, hy, hγy⟩ := Finsupp.mem_support_finsetSum γ hγ
    have hindex : γ = a y.1 y.2 := by
      simpa using Finsupp.support_single_subset hγy
    exact hindex ▸ ha y.1 y.2 t
  · have hd_repr : d = ∑ y ∈ d.support, Finsupp.single y (d y) := by
      simpa [Finsupp.sum] using (Finsupp.sum_single d).symm
    rw [hd_repr]
    simp only [B, A, map_sum, map_smul]
    rw [← Finset.sum_attach (s := d.support)
      (f := fun y => Finsupp.single y (d y))]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y hy
    rw [show Finsupp.single y.1 (d y.1) =
        (d y.1) • Finsupp.single y.1 1 by simp,
      show Finsupp.single (a y.1 y.2) (d y.1) =
        (d y.1) • Finsupp.single (a y.1 y.2) 1 by simp,
      map_smul, hb y.1 y.2]
    rw [smul_sub]
    congr 1
    simp [actualRegularChainsToSingular, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single]

theorem actualSingularEdge_regularize_in_open {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (U : Set E) (hU : IsOpen U)
    (σ : (TopCat.toSSet.obj (TopCat.of E)) _⦋1⦌)
    (hσ : ∀ u : StdSimplex ℝ (Fin 2),
      (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌) σ) u ∈ U) :
    ∃ a : ActualRegularOneChains E,
      (∀ γ ∈ a.support, ∀ t : ℝ, γ.toFun t ∈ U) ∧
      ∃ b : (TopCat.toSSet.obj (TopCat.of E)) _⦋2⦌ →₀ ℤ,
        singularBoundaryFinsupp (TopCat.of E) 1 b =
          Finsupp.single σ 1 - actualRegularChainsToSingular a := by
  obtain ⟨k, hk⟩ := actualSingularEdge_subdivided_openChartSmall U hU σ hσ
  let d := singularBarycentricIterate (TopCat.of E) 1 k (Finsupp.single σ 1)
  obtain ⟨a, ha, b, hb⟩ := actualOpenChartSmallSingularChain_regularize U d hk
  let H := singularCarrierHomotopyIterate (TopCat.of E) 1 k (Finsupp.single σ 1)
  have hH : singularBoundaryFinsupp (TopCat.of E) 1 H =
      d - Finsupp.single σ 1 := by
    have h := singularCarrierHomotopyIterate_boundary_succ
      (TopCat.of E) 0 k (Finsupp.single σ 1)
    rw [singularCarrierHomotopyIterate_degree_zero, add_zero] at h
    exact h
  refine ⟨a, ha, b - H, ?_⟩
  rw [map_sub, hb, hH]
  abel

end CanonicalDimensionTwo
