import CurveComplexGenusTwo.Topology.ActualIntervalLocalComparison.IntervalLocalCanceledFibers

open scoped Manifold ContDiff Bundle Simplicial
open Convexity CategoryTheory CurveComplexGenusTwo.CWHurewicz
open CanonicalDimensionTwo

namespace CanonicalDimensionTwo

set_option maxHeartbeats 1000000

theorem actualRegularChainsToSingular_filter {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (P : (TopCat.toSSet.obj (TopCat.of E)) _⦋1⦌ → Prop)
    [DecidablePred P] (a : ActualRegularOneChains E) :
    actualRegularChainsToSingular
      (Finsupp.filter (fun γ => P (actualRegularPathAsSingular γ)) a) =
      Finsupp.filter P (actualRegularChainsToSingular a) := by
  classical
  induction a using Finsupp.induction_linear with
  | zero =>
      have hz : Finsupp.filter
          (fun γ : ActualRegularPath E => P (actualRegularPathAsSingular γ))
          (0 : ActualRegularOneChains E) = 0 := by
        ext γ
        simp [Finsupp.filter_apply]
      rw [hz, map_zero]
      ext y
      simp [Finsupp.filter_apply]
  | add a b ha hb =>
      rw [Finsupp.filter_add, map_add, ha, hb, map_add, Finsupp.filter_add]
  | single γ n =>
      by_cases hP : P (actualRegularPathAsSingular γ)
      · ext y
        simp [actualRegularChainsToSingular,
          Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, hP]
      · ext y
        simp [actualRegularChainsToSingular,
          Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, hP]

theorem actualChartSmallBoundary_smallRegular_mem_relations {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (b : ActualSingularTwoChains E)
    (hsmall : ∀ σ ∈ b.support, ∃ i : ActualChartBallIndex E,
      ∀ u : StdSimplex ℝ (Fin 3),
        (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋2⦌) σ) u ∈
          actualChartBallCover i)
    (z : ActualRegularOneCycles E)
    (hboundary : singularBoundaryFinsupp (TopCat.of E) 1 b =
      actualRegularChainsToSingular z.1)
    (hsmallz : ∀ γ ∈ z.1.support,
      ∃ i : ActualChartBallIndex E,
        ∀ u : StdSimplex ℝ (Fin 2),
          (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌)
            (actualRegularPathAsSingular γ)) u ∈ actualChartBallCover i) :
    z ∈ intervalLocalNormalizedRelations (E := E) := by
  classical
  let P : (TopCat.toSSet.obj (TopCat.of E)) _⦋1⦌ → Prop :=
    fun y => y ∈ actualFaceSet b
  let af : ActualRegularOneChains E :=
    Finsupp.filter (fun γ => P (actualRegularPathAsSingular γ)) z.1
  let ac : ActualRegularOneChains E :=
    Finsupp.filter (fun γ => ¬ P (actualRegularPathAsSingular γ)) z.1
  have hsplit : z.1 = af + ac := by
    ext γ
    simp only [af, ac, Finsupp.add_apply, Finsupp.filter_apply]
    by_cases h : P (actualRegularPathAsSingular γ) <;> simp [h]
  have hface : ∀ γ ∈ af.support,
      actualRegularPathAsSingular γ ∈ actualFaceSet b := by
    intro γ hγ
    change γ ∈ (Finsupp.filter
      (fun γ => P (actualRegularPathAsSingular γ)) z.1).support at hγ
    rw [Finsupp.support_filter] at hγ
    exact (Finset.mem_filter.mp hγ).2
  have hsf : actualRegularChainsToSingular af =
      singularBoundaryFinsupp (TopCat.of E) 1 b := by
    change actualRegularChainsToSingular
      (Finsupp.filter (fun γ => P (actualRegularPathAsSingular γ)) z.1) = _
    rw [actualRegularChainsToSingular_filter P z.1]
    rw [← hboundary]
    ext y
    simp only [Finsupp.filter_apply]
    by_cases hy : y ∈ actualFaceSet b
    · simp [P, hy]
    · have hzero : (singularBoundaryFinsupp (TopCat.of E) 1 b) y = 0 := by
        by_contra hne
        have hm : y ∈ (singularBoundaryFinsupp (TopCat.of E) 1 b).support :=
          Finsupp.mem_support_iff.mpr hne
        exact hy (actualSingularTwoBoundary_support_faceSet b hm)
      simp [P, hy, hzero]
  have hsc : actualRegularChainsToSingular ac = 0 := by
    rw [hsplit, map_add, hsf] at hboundary
    have heq : singularBoundaryFinsupp (TopCat.of E) 1 b +
        actualRegularChainsToSingular ac =
      singularBoundaryFinsupp (TopCat.of E) 1 b + 0 := by
      simpa using hboundary.symm
    exact add_left_cancel heq
  obtain ⟨zc, hzc, hrc⟩ := actualRegularSmallCanceledChain_mem_relations ac
    hsc (by
      intro γ hγ
      have hs : γ ∈ z.1.support := by
        change γ ∈ (Finsupp.filter
          (fun γ => ¬ P (actualRegularPathAsSingular γ)) z.1).support at hγ
        rw [Finsupp.support_filter] at hγ
        exact (Finset.mem_filter.mp hγ).1
      exact hsmallz γ hs)
  have hbf : actualRegularChainBoundary af = 0 := by
    have h := LinearMap.congr_fun
      (actualRegularChainsToSingular_boundary (E := E)) af
    change singularBoundaryFinsupp (TopCat.of E) 0
      (actualRegularChainsToSingular af) =
      actualRegularPointsToSingular (actualRegularChainBoundary af) at h
    rw [hsf, singularBoundaryFinsupp_comp_zero] at h
    exact actualRegularPointsToSingular_injective (by simpa using h.symm)
  let zf : ActualRegularOneCycles E := ⟨af, hbf⟩
  have hzf : zf ∈ intervalLocalNormalizedRelations (E := E) :=
    actualChartSmallBoundary_faceSupported_mem_relations b hsmall zf
      (by exact hsf.symm) (by exact hface)
  have hsum := (intervalLocalNormalizedRelations (E := E)).add_mem hzf hrc
  have hz : z = zf + zc := by
    apply Subtype.ext
    change z.1 = af + zc.1
    rw [hzc]
    exact hsplit
  rwa [hz]

theorem intervalLocalNormalizedRelations_complete {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (z : ActualRegularOneCycles E)
    (hz : actualRegularCyclesToSingular z ∈ actualSingularTwoBoundaries E) :
    z ∈ intervalLocalNormalizedRelations (E := E) := by
  classical
  change actualRegularCyclesToSingular z ∈
    LinearMap.range (LinearMap.codRestrict (ActualSingularOneCycles E)
      (singularBoundaryFinsupp (TopCat.of E) 1) (fun c => by
        exact singularBoundaryFinsupp_comp_zero (TopCat.of E) 0 c)) at hz
  obtain ⟨b, hb⟩ := hz
  have hboundary : singularBoundaryFinsupp (TopCat.of E) 1 b =
      actualRegularChainsToSingular z.1 := by
    have h := congrArg Subtype.val hb
    change singularBoundaryFinsupp (TopCat.of E) 1 b =
      actualRegularChainsToSingular z.1 at h
    exact h
  obtain ⟨k1, hsmall1⟩ := actualRegularSignedIterate_chartSmall z.1
  let z1 : ActualRegularOneCycles E :=
    ⟨actualRegularSignedIterate k1 z.1, by
      change actualRegularChainBoundary _ = 0
      rw [actualRegularSignedIterate_boundary]
      exact z.2⟩
  let b1 : ActualSingularTwoChains E :=
    singularBarycentricIterate (TopCat.of E) 2 k1 b
  have hboundary1 : singularBoundaryFinsupp (TopCat.of E) 1 b1 =
      actualRegularChainsToSingular z1.1 := by
    change singularBoundaryFinsupp (TopCat.of E) 1
        (singularBarycentricIterate (TopCat.of E) 2 k1 b) =
      actualRegularChainsToSingular (actualRegularSignedIterate k1 z.1)
    rw [singularBarycentricIterate_boundary, hboundary,
      actualRegularSignedIterate_singular]
  obtain ⟨k2, hsmall2⟩ := actualSingularBarycentricIterate_chartSmall 2 b1
  let b2 : ActualSingularTwoChains E :=
    singularBarycentricIterate (TopCat.of E) 2 k2 b1
  let z2 : ActualRegularOneCycles E :=
    ⟨actualRegularSignedIterate k2 z1.1, by
      change actualRegularChainBoundary _ = 0
      rw [actualRegularSignedIterate_boundary]
      exact z1.2⟩
  have hboundary2 : singularBoundaryFinsupp (TopCat.of E) 1 b2 =
      actualRegularChainsToSingular z2.1 := by
    change singularBoundaryFinsupp (TopCat.of E) 1
        (singularBarycentricIterate (TopCat.of E) 2 k2 b1) =
      actualRegularChainsToSingular (actualRegularSignedIterate k2 z1.1)
    calc
      _ = singularBarycentricIterate (TopCat.of E) 1 k2
          (actualRegularChainsToSingular z1.1) := by
            rw [singularBarycentricIterate_boundary, hboundary1]
      _ = actualRegularChainsToSingular
          (actualRegularSignedIterate k2 z1.1) :=
            (actualRegularSignedIterate_singular k2 z1.1).symm
  have hsmallz2 : ∀ γ ∈ z2.1.support,
      ∃ i : ActualChartBallIndex E,
        ∀ u : StdSimplex ℝ (Fin 2),
          (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌)
            (actualRegularPathAsSingular γ)) u ∈ actualChartBallCover i := by
    intro γ hγ
    exact actualRegularSignedIterate_chartSmall_preserve z1.1 hsmall1 k2 γ hγ
  have hz2 : z2 ∈ intervalLocalNormalizedRelations (E := E) :=
    actualChartSmallBoundary_smallRegular_mem_relations b2 hsmall2 z2
      hboundary2 hsmallz2
  have hdiff2 : z1 - z2 ∈ intervalLocalNormalizedRelations (E := E) := by
    convert actualRegularSignedIterate_difference_mem_relations k2 z1 using 1
  have hz1 : z1 ∈ intervalLocalNormalizedRelations (E := E) := by
    have heq : z1 = (z1 - z2) + z2 := by abel
    rw [heq]
    exact (intervalLocalNormalizedRelations (E := E)).add_mem hdiff2 hz2
  have hdiff1 : z - z1 ∈ intervalLocalNormalizedRelations (E := E) := by
    convert actualRegularSignedIterate_difference_mem_relations k1 z using 1
  have heq : z = (z - z1) + z1 := by abel
  rw [heq]
  exact (intervalLocalNormalizedRelations (E := E)).add_mem hdiff1 hz1

theorem intervalLocalNormalizedRegularHOneToSingular_injective {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    Function.Injective (intervalLocalNormalizedRegularHOneToSingular (E := E)) := by
  intro x y hxy
  have hker : intervalLocalNormalizedRegularHOneToSingular (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨z, hz⟩ := (intervalLocalNormalizedRelations (E := E)).mkQ_surjective
    (x - y)
  rw [← hz, intervalLocalNormalizedRegularHOneToSingular_mk] at hker
  have hbound : actualRegularCyclesToSingular z ∈ actualSingularTwoBoundaries E :=
    (Submodule.Quotient.mk_eq_zero _).mp hker
  have hrel := intervalLocalNormalizedRelations_complete z hbound
  have hzero : x - y = 0 := by
    rw [← hz]
    exact (Submodule.Quotient.mk_eq_zero _).mpr hrel
  exact sub_eq_zero.mp hzero

theorem intervalLocalNormalizedRegularHOneToSingular_bijective {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    Function.Bijective (intervalLocalNormalizedRegularHOneToSingular (E := E)) :=
  ⟨intervalLocalNormalizedRegularHOneToSingular_injective,
    intervalLocalNormalizedRegularHOneToSingular_surjective⟩

theorem intervalLocalNormalizedRegularHOneToProject_bijective {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    Function.Bijective (intervalLocalNormalizedRegularHOneToProject (E := E)) := by
  constructor
  · intro x y hxy
    apply intervalLocalNormalizedRegularHOneToSingular_injective
    have h := congrArg (actualSingularHOneIsoProject E).inv.hom hxy
    simpa [intervalLocalNormalizedRegularHOneToProject,
      (actualSingularHOneIsoProject E).hom_inv_id_apply] using h
  · exact intervalLocalNormalizedRegularHOneToProject_surjective

end CanonicalDimensionTwo
