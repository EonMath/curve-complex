import CurveComplexGenusTwo.Topology.ActualIntervalLocalComparison.NormalizedRegularHOne

open scoped Manifold ContDiff Bundle Simplicial
open CategoryTheory CurveComplexGenusTwo.CWHurewicz
open CanonicalDimensionTwo

namespace CanonicalDimensionTwo

theorem actualNormalizedRelationSet_period_zero {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (z : ActualRegularOneCycles E)
    (hz : z ∈ actualNormalizedRelationSet (E := E)) :
    actualRegularCyclePeriod s z = 0 := by
  simp only [actualNormalizedRelationSet, Set.mem_union] at hz
  rcases hz with (((h | h) | h) | h)
  · obtain ⟨c, rfl⟩ := h
    exact actualRegularCyclePeriod_vanishes_on_chart_boundaries s ⟨c, rfl⟩
  · obtain ⟨x, rfl⟩ := h
    exact actualRegularConstantCycle_period_zero s x
  · obtain ⟨γ, rfl⟩ := h
    exact actualRegularChainIntegral_reverse s γ
  · obtain ⟨γ, rfl⟩ := h
    exact actualRegularSubdivision_period_zero s γ

theorem actualNormalizedRelations_period_zero {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) :
    actualNormalizedRelations (E := E) ≤
      (actualRegularCyclePeriod s).ker := by
  apply Submodule.span_le.mpr
  intro z hz
  exact actualNormalizedRelationSet_period_zero s z hz

theorem actualNormalizedRelationSet_singular_boundary {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (z : ActualRegularOneCycles E)
    (hz : z ∈ actualNormalizedRelationSet (E := E)) :
    actualRegularCyclesToSingular z ∈ actualSingularTwoBoundaries E := by
  simp only [actualNormalizedRelationSet, Set.mem_union] at hz
  rcases hz with (((h | h) | h) | h)
  · obtain ⟨c, rfl⟩ := h
    exact actualRegularCyclesToSingular_chart_boundary ⟨c, rfl⟩
  · obtain ⟨x, rfl⟩ := h
    have hq := actualRegularConstantCycle_maps_zero x
    rw [actualRegularChartHomologyToSingular_mk] at hq
    exact (Submodule.Quotient.mk_eq_zero _).mp hq
  · obtain ⟨γ, rfl⟩ := h
    exact actualRegularReverseCycle_singular_boundary γ
  · obtain ⟨γ, rfl⟩ := h
    exact actualRegularSubdivisionCycle_singular_boundary γ

theorem actualNormalizedRelations_singular_boundary {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    actualNormalizedRelations (E := E) ≤
      (actualSingularTwoBoundaries E).comap
        (actualRegularCyclesToSingular (E := E)) := by
  apply Submodule.span_le.mpr
  intro z hz
  exact actualNormalizedRelationSet_singular_boundary z hz

noncomputable def actualNormalizedRegularPeriod {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) : ActualNormalizedRegularHOne E →ₗ[ℤ] ℂ :=
  (actualNormalizedRelations (E := E)).liftQ
    (actualRegularCyclePeriod s)
    (actualNormalizedRelations_period_zero s)

theorem actualNormalizedRegularPeriod_mk {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (z : ActualRegularOneCycles E) :
    actualNormalizedRegularPeriod s
      ((actualNormalizedRelations (E := E)).mkQ z) =
      actualRegularCyclePeriod s z := rfl

noncomputable def actualNormalizedRegularHOneToSingular {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    ActualNormalizedRegularHOne E →ₗ[ℤ] ActualSingularHOne E :=
  (actualNormalizedRelations (E := E)).liftQ
    ((actualSingularTwoBoundaries E).mkQ.comp
      (actualRegularCyclesToSingular (E := E))) (by
        intro z hz
        exact Submodule.Quotient.mk_eq_zero _ |>.mpr
          (actualNormalizedRelations_singular_boundary (E := E) hz))

theorem actualNormalizedRegularHOneToSingular_mk {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (z : ActualRegularOneCycles E) :
    actualNormalizedRegularHOneToSingular
      ((actualNormalizedRelations (E := E)).mkQ z) =
      (actualSingularTwoBoundaries E).mkQ
        (actualRegularCyclesToSingular z) := rfl

noncomputable def actualNormalizedRegularHOneToProject {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    ActualNormalizedRegularHOne E →ₗ[ℤ]
      CurveComplex.integralHomology E 1 :=
  (actualSingularHOneIsoProject E).hom.hom.comp
    (actualNormalizedRegularHOneToSingular (E := E))

theorem actualNormalizedRegularHOneToProject_mk {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (z : ActualRegularOneCycles E) :
    actualNormalizedRegularHOneToProject
      ((actualNormalizedRelations (E := E)).mkQ z) =
      (actualSingularHOneIsoProject E).hom.hom
        ((actualSingularTwoBoundaries E).mkQ
          (actualRegularCyclesToSingular z)) := by
  exact congrArg (actualSingularHOneIsoProject E).hom.hom
    (actualNormalizedRegularHOneToSingular_mk z)

theorem actualNormalizedRegularHOneToSingular_surjective {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    Function.Surjective (actualNormalizedRegularHOneToSingular (E := E)) := by
  intro z
  obtain ⟨c, rfl⟩ := (actualSingularTwoBoundaries E).mkQ_surjective z
  obtain ⟨a, b, hb⟩ :=
    actualSingularOneCycle_regularize_cycle c.1 c.2
  refine ⟨(actualNormalizedRelations (E := E)).mkQ a, ?_⟩
  rw [actualNormalizedRegularHOneToSingular_mk]
  apply Submodule.Quotient.eq _ |>.mpr
  change actualRegularCyclesToSingular a - c ∈ actualSingularTwoBoundaries E
  refine ⟨-b, ?_⟩
  apply Subtype.ext
  change singularBoundaryFinsupp (TopCat.of E) 1 (-b) =
    actualRegularChainsToSingular a.1 - c.1
  rw [map_neg, hb]
  abel

theorem actualNormalizedRegularHOneToProject_surjective {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    Function.Surjective (actualNormalizedRegularHOneToProject (E := E)) := by
  intro z
  let y := (actualSingularHOneIsoProject E).inv z
  have hy : (actualSingularHOneIsoProject E).hom y = z := by
    exact (actualSingularHOneIsoProject E).inv_hom_id_apply z
  rw [← hy]
  obtain ⟨x, hx⟩ := actualNormalizedRegularHOneToSingular_surjective y
  refine ⟨x, ?_⟩
  change (actualSingularHOneIsoProject E).hom
    (actualNormalizedRegularHOneToSingular x) = _
  rw [hx]

end CanonicalDimensionTwo
