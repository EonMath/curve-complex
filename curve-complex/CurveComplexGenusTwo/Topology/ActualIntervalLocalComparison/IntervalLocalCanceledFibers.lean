import CurveComplexGenusTwo.Topology.ActualIntervalLocalComparison.IntervalLocalRegularSmallness

open scoped Manifold ContDiff Bundle Simplicial
open Convexity CategoryTheory CurveComplexGenusTwo.CWHurewicz
open CanonicalDimensionTwo

namespace CanonicalDimensionTwo

set_option maxHeartbeats 1000000

theorem actualRegularSameSingular_interval_eq {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (γ δ : ActualRegularPath E)
    (h : actualRegularPathAsSingular γ = actualRegularPathAsSingular δ)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    γ.toFun t = δ.toFun t := by
  let u := TopCat.stdSimplexHomeomorphI.{0}.symm ⟨t, ht⟩
  have hu := congrArg
    (fun y => (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌) y) u) h
  simpa [u, actualRegularPathAsSingular] using hu

noncomputable def actualSameSingularDifferenceCycle {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (γ δ : ActualRegularPath E)
    (h : actualRegularPathAsSingular γ = actualRegularPathAsSingular δ) :
    ActualRegularOneCycles E :=
  ⟨Finsupp.single γ 1 - Finsupp.single δ 1, by
    change actualRegularChainBoundary _ = 0
    rw [map_sub, actualRegularChainBoundary_single,
      actualRegularChainBoundary_single]
    have h0 := actualRegularSameSingular_interval_eq γ δ h 0 (by norm_num)
    have h1 := actualRegularSameSingular_interval_eq γ δ h 1 (by norm_num)
    rw [h0, h1]
    abel⟩

theorem actualRegularSameSingular_localDifference_mem {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (γ δ : ActualRegularPath E)
    (h : actualRegularPathAsSingular γ = actualRegularPathAsSingular δ)
    (i : ActualChartBallIndex E)
    (hγ : ∀ u : StdSimplex ℝ (Fin 2),
      (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌)
        (actualRegularPathAsSingular γ)) u ∈ actualChartBallCover i) :
    actualSameSingularDifferenceCycle γ δ h ∈
      intervalLocalNormalizedRelations (E := E) := by
  have h0 := actualRegularSameSingular_interval_eq γ δ h 0 (by norm_num)
  have h1 := actualRegularSameSingular_interval_eq γ δ h 1 (by norm_num)
  have hγloc : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ.toFun t ∈ actualChartBallCover i := by
    intro t ht
    let u := TopCat.stdSimplexHomeomorphI.{0}.symm ⟨t, ht⟩
    simpa [u, actualRegularPathAsSingular] using hγ u
  have hδloc : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      δ.toFun t ∈ actualChartBallCover i := by
    intro t ht
    rw [← actualRegularSameSingular_interval_eq γ δ h t ht]
    exact hγloc t ht
  have hmem := intervalLocalParallelRegularDifference_mem_normalized
    i.q i.c i.r i.target γ δ
    (fun t ht => (hγloc t ht).1)
    (fun t ht => (hγloc t ht).2)
    (fun t ht => (hδloc t ht).1)
    (fun t ht => (hδloc t ht).2) h0 h1
  convert hmem using 1
  apply Subtype.ext
  rfl

theorem actualRegularSmallCanceledChain_mem_relations {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (a : ActualRegularOneChains E)
    (hzero : actualRegularChainsToSingular a = 0)
    (hsmall : ∀ γ ∈ a.support,
      ∃ i : ActualChartBallIndex E,
        ∀ u : StdSimplex ℝ (Fin 2),
          (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌)
            (actualRegularPathAsSingular γ)) u ∈ actualChartBallCover i) :
    ∃ z : ActualRegularOneCycles E,
      z.1 = a ∧ z ∈ intervalLocalNormalizedRelations (E := E) := by
  classical
  let f : ActualRegularPath E →
      (TopCat.toSSet.obj (TopCat.of E)) _⦋1⦌ := actualRegularPathAsSingular
  let s := a.support.image f
  let rep : s → ActualRegularPath E := fun y =>
    Classical.choose (Finset.mem_image.mp y.2)
  have hrep (y : s) : rep y ∈ a.support ∧ f (rep y) = y.1 := by
    exact Classical.choose_spec (Finset.mem_image.mp y.2)
  let d : ActualRegularOneCycles E :=
    ∑ y ∈ s.attach, ∑ γ ∈ a.support.attach,
      if heq : f γ.1 = y.1 then
        (a γ.1) • actualSameSingularDifferenceCycle γ.1 (rep y)
          (heq.trans (hrep y).2.symm)
      else 0
  have hd : d ∈ intervalLocalNormalizedRelations (E := E) := by
    dsimp [d]
    apply Submodule.sum_mem
    intro y hy
    apply Submodule.sum_mem
    intro γ hγ
    split_ifs with heq
    · obtain ⟨i, hi⟩ := hsmall γ.1 γ.2
      exact (intervalLocalNormalizedRelations (E := E)).smul_mem _
        (actualRegularSameSingular_localDifference_mem γ.1 (rep y)
          (heq.trans (hrep y).2.symm) i hi)
    · exact (intervalLocalNormalizedRelations (E := E)).zero_mem
  refine ⟨d, ?_, hd⟩
  have hcoef (y : s) :
      (∑ γ ∈ a.support.attach,
        if f γ.1 = y.1 then a γ.1 else 0) = 0 := by
    have hy := congrArg (fun c : ActualSingularOneChains E => c y.1) hzero
    change (Finsupp.mapDomain f a) y.1 = 0 at hy
    rw [Finsupp.mapDomain_apply] at hy
    simp only [Finsupp.sum] at hy
    rw [← Finset.sum_attach] at hy
    simpa [Finsupp.single_apply] using hy
  have hrepr : a = ∑ γ ∈ a.support, a γ • Finsupp.single γ 1 := by
    conv_lhs => rw [← Finsupp.sum_single a]
    simp [Finsupp.sum, Finsupp.smul_single]
  change d.1 = a
  dsimp [d]
  simp only [Submodule.coe_sum]
  have hterm (y : s) (γ : a.support) :
      ((↑(if heq : f γ.1 = y.1 then
        (a γ.1) • actualSameSingularDifferenceCycle γ.1 (rep y)
          (heq.trans (hrep y).2.symm)
        else 0) : ActualRegularOneChains E)) =
      if f γ.1 = y.1 then
        (a γ.1) • (Finsupp.single γ.1 1 - Finsupp.single (rep y) 1)
      else 0 := by
    split_ifs <;> rfl
  simp_rw [hterm]
  have hinner (y : s) :
      (∑ γ ∈ a.support.attach,
        if f γ.1 = y.1 then
          a γ.1 • ((Finsupp.single γ.1 1 - Finsupp.single (rep y) 1) :
            ActualRegularOneChains E)
        else 0) =
      ∑ γ ∈ a.support.attach,
        if f γ.1 = y.1 then
          a γ.1 • (Finsupp.single γ.1 (1 : ℤ) : ActualRegularOneChains E)
        else 0 := by
    have hsplit :
        (∑ γ ∈ a.support.attach,
          if f γ.1 = y.1 then
            a γ.1 • ((Finsupp.single γ.1 1 - Finsupp.single (rep y) 1) :
              ActualRegularOneChains E)
          else 0) =
        (∑ γ ∈ a.support.attach,
          if f γ.1 = y.1 then
            a γ.1 • (Finsupp.single γ.1 (1 : ℤ) : ActualRegularOneChains E)
          else 0) -
        (∑ γ ∈ a.support.attach,
          if f γ.1 = y.1 then
            a γ.1 • (Finsupp.single (rep y) (1 : ℤ) : ActualRegularOneChains E)
          else 0) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro γ hγ
      split_ifs <;> simp [smul_sub]
    have hvanish : (∑ γ ∈ a.support.attach,
        if f γ.1 = y.1 then
          a γ.1 • (Finsupp.single (rep y) (1 : ℤ) : ActualRegularOneChains E)
        else 0) = 0 := by
      rw [← Finset.sum_filter]
      rw [← Finset.sum_smul]
      rw [Finset.sum_filter]
      rw [hcoef y]
      simp
    rw [hsplit, hvanish]
    abel
  simp_rw [hinner]
  let g : a.support → s := fun γ =>
    ⟨f γ.1, Finset.mem_image.mpr ⟨γ.1, γ.2, rfl⟩⟩
  simp_rw [← Finset.sum_filter]
  have hfilter (y : s) :
      (a.support.attach.filter (fun γ => f γ.1 = y.1)) =
        a.support.attach.filter (fun γ => g γ = y) := by
    apply Finset.filter_congr
    intro γ hγ
    change f γ.1 = y.1 ↔
      (⟨f γ.1, _⟩ : s) = y
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      exact congrArg Subtype.val h
  simp_rw [hfilter]
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := a.support.attach) (t := s.attach) (g := g)
    (fun γ hγ => Finset.mem_attach _ _) (fun γ : a.support =>
      a γ.1 • (Finsupp.single γ.1 (1 : ℤ) : ActualRegularOneChains E))
  rw [hfiber]
  exact (Finset.sum_attach _ _).trans hrepr.symm

end CanonicalDimensionTwo
