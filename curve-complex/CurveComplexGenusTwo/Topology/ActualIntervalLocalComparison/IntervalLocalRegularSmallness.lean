import CurveComplexGenusTwo.Topology.ActualIntervalLocalComparison.IntervalLocalSharedComparison

open scoped Manifold ContDiff Bundle Simplicial
open Convexity CategoryTheory CurveComplexGenusTwo.CWHurewicz
open CanonicalDimensionTwo

namespace CanonicalDimensionTwo

set_option maxHeartbeats 1000000

noncomputable def actualRegularFlagStep {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (σ : Equiv.Perm (Fin 2)) (γ : ActualRegularPath E) : ActualRegularPath E :=
  if σ = 1 then γ.leftHalf else γ.rightHalf.reverse

theorem actualRegularFlagStep_singular {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (σ : Equiv.Perm (Fin 2)) (γ : ActualRegularPath E) :
    actualRegularPathAsSingular (actualRegularFlagStep σ γ) =
      barycentricFlagSingular (TopCat.of E) 1 σ
        (actualRegularPathAsSingular γ) := by
  have hσ : σ = 1 ∨ σ = Equiv.swap 0 1 := by
    have h : (Finset.univ : Finset (Equiv.Perm (Fin 2))) =
        {1, Equiv.swap 0 1} := by decide
    have hm : σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin 2))) := Finset.mem_univ _
    rw [h, Finset.mem_insert, Finset.mem_singleton] at hm
    exact hm
  rcases hσ with rfl | rfl
  · simp [actualRegularFlagStep, actualBarycentricFlag_id_regular_leftHalf]
  · have hne : (Equiv.swap (0 : Fin 2) 1) ≠ 1 := by decide
    simp [actualRegularFlagStep, hne,
      actualBarycentricFlag_swap_regular_reverseRight]

noncomputable def actualRegularFlagIterate {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (ss : List (Equiv.Perm (Fin 2))) (γ : ActualRegularPath E) :
    ActualRegularPath E :=
  match ss with
  | [] => γ
  | σ :: tail => actualRegularFlagStep σ (actualRegularFlagIterate tail γ)

theorem actualRegularFlagIterate_singular {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (ss : List (Equiv.Perm (Fin 2))) (γ : ActualRegularPath E) :
    actualRegularPathAsSingular (actualRegularFlagIterate ss γ) =
      singularFlagIterate (TopCat.of E) 1 ss
        (actualRegularPathAsSingular γ) := by
  induction ss with
  | nil => rfl
  | cons σ ss ih =>
      rw [actualRegularFlagIterate, actualRegularFlagStep_singular, ih]
      rfl

theorem actualRegularSignedSubdivision_support {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (a : ActualRegularOneChains E) (δ : ActualRegularPath E)
    (hδ : δ ∈ (actualRegularSignedSubdivision a).support) :
    ∃ γ ∈ a.support, ∃ σ : Equiv.Perm (Fin 2),
      δ = actualRegularFlagStep σ γ := by
  classical
  have hrepr : a = ∑ γ ∈ a.support, a γ • Finsupp.single γ 1 := by
    conv_lhs => rw [← Finsupp.sum_single a]
    simp [Finsupp.sum, Finsupp.smul_single]
  rw [hrepr, map_sum] at hδ
  obtain ⟨γ, hγ, hδγ⟩ := Finsupp.mem_support_finsetSum δ hδ
  rw [map_smul] at hδγ
  have hδ' := Finsupp.support_smul hδγ
  change δ ∈ (actualRegularSignedSubdivision
    (Finsupp.single γ 1)).support at hδ'
  simp only [actualRegularSignedSubdivision, Finsupp.linearCombination_single,
    one_smul] at hδ'
  rcases Finset.mem_union.mp (Finsupp.support_sub hδ') with h | h
  · have heq : δ = γ.leftHalf := by simpa using h
    exact ⟨γ, hγ, 1, by simpa [actualRegularFlagStep] using heq⟩
  · have heq : δ = γ.rightHalf.reverse := by simpa using h
    exact ⟨γ, hγ, Equiv.swap 0 1, by
      simpa [actualRegularFlagStep, show (Equiv.swap (0 : Fin 2) 1) ≠ 1 by decide]
        using heq⟩

theorem actualRegularSignedIterate_support {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (k : ℕ) (a : ActualRegularOneChains E) (δ : ActualRegularPath E)
    (hδ : δ ∈ (actualRegularSignedIterate k a).support) :
    ∃ γ ∈ a.support, ∃ ss : List (Equiv.Perm (Fin 2)),
      ss.length = k ∧ δ = actualRegularFlagIterate ss γ := by
  induction k generalizing δ with
  | zero =>
      exact ⟨δ, by simpa [actualRegularSignedIterate] using hδ,
        [], rfl, by simp [actualRegularFlagIterate]⟩
  | succ k ih =>
      have hδ' : δ ∈ (actualRegularSignedSubdivision
          (actualRegularSignedIterate k a)).support := by
        simpa [actualRegularSignedIterate] using hδ
      obtain ⟨η, hη, σ, rfl⟩ :=
        actualRegularSignedSubdivision_support _ _ hδ'
      obtain ⟨γ, hγ, ss, hlen, rfl⟩ := ih η hη
      exact ⟨γ, hγ, σ :: ss, by simp [hlen], rfl⟩

theorem actualRegularSignedIterate_chartSmall {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (a : ActualRegularOneChains E) :
    ∃ k : ℕ, ∀ δ ∈ (actualRegularSignedIterate k a).support,
      ∃ i : ActualChartBallIndex E,
        ∀ u : StdSimplex ℝ (Fin 2),
          (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌)
            (actualRegularPathAsSingular δ)) u ∈ actualChartBallCover i := by
  let fs : List ((TopCat.toSSet.obj (TopCat.of E)) _⦋1⦌) :=
    a.support.toList.map actualRegularPathAsSingular
  obtain ⟨k, hk⟩ := actualSingularSimplexFamily_chartBallSubdivision 1 fs
  refine ⟨k, ?_⟩
  intro δ hδ
  obtain ⟨γ, hγ, ss, hlen, rfl⟩ :=
    actualRegularSignedIterate_support k a δ hδ
  have hmem : actualRegularPathAsSingular γ ∈ fs := by
    exact List.mem_map.mpr ⟨γ, by simpa [fs] using hγ, rfl⟩
  obtain ⟨i, hi⟩ := hk _ hmem ss hlen
  refine ⟨i, ?_⟩
  intro u
  rw [actualRegularFlagIterate_singular,
    singularFlagIterate_eval]
  exact hi u

theorem actualRegularSignedSubdivision_chartSmall_preserve {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (a : ActualRegularOneChains E)
    (hsmall : ∀ γ ∈ a.support,
      ∃ i : ActualChartBallIndex E,
        ∀ u : StdSimplex ℝ (Fin 2),
          (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌)
            (actualRegularPathAsSingular γ)) u ∈ actualChartBallCover i)
    (δ : ActualRegularPath E)
    (hδ : δ ∈ (actualRegularSignedSubdivision a).support) :
    ∃ i : ActualChartBallIndex E,
      ∀ u : StdSimplex ℝ (Fin 2),
        (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌)
          (actualRegularPathAsSingular δ)) u ∈ actualChartBallCover i := by
  obtain ⟨γ, hγ, σ, rfl⟩ :=
    actualRegularSignedSubdivision_support a δ hδ
  obtain ⟨i, hi⟩ := hsmall γ hγ
  refine ⟨i, ?_⟩
  intro u
  rw [actualRegularFlagStep_singular]
  change (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌)
      (actualRegularPathAsSingular γ)) (barycentricFlag 1 σ u) ∈ _
  exact hi _

theorem actualRegularSignedIterate_chartSmall_preserve {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (a : ActualRegularOneChains E)
    (hsmall : ∀ γ ∈ a.support,
      ∃ i : ActualChartBallIndex E,
        ∀ u : StdSimplex ℝ (Fin 2),
          (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌)
            (actualRegularPathAsSingular γ)) u ∈ actualChartBallCover i)
    (k : ℕ) (δ : ActualRegularPath E)
    (hδ : δ ∈ (actualRegularSignedIterate k a).support) :
    ∃ i : ActualChartBallIndex E,
      ∀ u : StdSimplex ℝ (Fin 2),
        (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌)
          (actualRegularPathAsSingular δ)) u ∈ actualChartBallCover i := by
  induction k generalizing δ with
  | zero => exact hsmall δ (by simpa [actualRegularSignedIterate] using hδ)
  | succ k ih =>
      change δ ∈ (actualRegularSignedSubdivision
        (actualRegularSignedIterate k a)).support at hδ
      exact actualRegularSignedSubdivision_chartSmall_preserve _
        (fun γ hγ => ih γ hγ) δ hδ

end CanonicalDimensionTwo
