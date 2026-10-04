import CurveComplexGenusTwo.Topology.ActualIntervalLocalComparison.IntervalLocalSharedFilling

open scoped Manifold ContDiff Bundle Simplicial
open Convexity CategoryTheory CurveComplexGenusTwo.CWHurewicz
open CanonicalDimensionTwo

namespace CanonicalDimensionTwo

theorem actualFlagOneIdCoordinate (t : StdSimplex ℝ (Fin 2)) :
    (barycentricFlag 1 (1 : Equiv.Perm (Fin 2)) t).weights 1 =
      t.weights 1 / 2 := by
  change (StdSimplex.iConvexComb t
    (fun k => StdSimplex.subBarycenter
      (Finset.univ.filter (fun i : Fin 2 => (1 : Equiv.Perm (Fin 2)).symm i ≤ k))
      (by
        refine ⟨(1 : Equiv.Perm (Fin 2)) 0, ?_⟩
        fin_cases k <;> decide))).weights 1 = _
  rw [StdSimplex.weights_iConvexComb]
  rw [Finsupp.sum_fintype _ _ (by simp)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, add_zero, smul_eq_mul]
  have hs0 : (Finset.univ.filter
      (fun i : Fin 2 => (1 : Equiv.Perm (Fin 2)).symm i ≤ (0 : Fin 2))) =
      {0} := by decide
  have hs1 : (Finset.univ.filter
      (fun i : Fin 2 => (1 : Equiv.Perm (Fin 2)).symm i ≤ (1 : Fin 2))) =
      Finset.univ := by decide
  simp only [show (Fin.succ (0 : Fin 1)) = (1 : Fin 2) from rfl]
  simp only [hs0, hs1]
  rw [StdSimplex.subBarycenter_singleton]
  norm_num [StdSimplex.weights_barycenter_apply]
  ring

theorem actualFlagOneSwapCoordinate (t : StdSimplex ℝ (Fin 2)) :
    (barycentricFlag 1 (Equiv.swap 0 1) t).weights 1 =
      1 - t.weights 1 / 2 := by
  change (StdSimplex.iConvexComb t
    (fun k => StdSimplex.subBarycenter
      (Finset.univ.filter (fun i : Fin 2 => (Equiv.swap 0 1).symm i ≤ k))
      (by
        refine ⟨(Equiv.swap 0 1) 0, ?_⟩
        fin_cases k <;> decide))).weights 1 = _
  rw [StdSimplex.weights_iConvexComb]
  rw [Finsupp.sum_fintype _ _ (by simp)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero,
    Finsupp.add_apply, Finsupp.smul_apply, add_zero, smul_eq_mul]
  have hs0 : (Finset.univ.filter
      (fun i : Fin 2 => (Equiv.swap 0 1).symm i ≤ (0 : Fin 2))) =
      {1} := by decide
  have hs1 : (Finset.univ.filter
      (fun i : Fin 2 => (Equiv.swap 0 1).symm i ≤ (1 : Fin 2))) =
      Finset.univ := by decide
  simp only [show (Fin.succ (0 : Fin 1)) = (1 : Fin 2) from rfl]
  simp only [hs0, hs1]
  rw [StdSimplex.subBarycenter_singleton]
  norm_num [StdSimplex.weights_barycenter_apply]
  have ht : t.weights 0 + t.weights 1 = 1 := by simp
  linear_combination ht

theorem actualBarycentricFlag_id_regular_leftHalf {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (γ : ActualRegularPath E) :
    barycentricFlagSingular (TopCat.of E) 1 1
      (actualRegularPathAsSingular γ) =
      actualRegularPathAsSingular γ.leftHalf := by
  apply (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌)).injective
  apply ContinuousMap.ext
  intro t
  change γ.toFun ((barycentricFlag 1 1 t).weights 1) =
    γ.toFun (((TopCat.stdSimplexHomeomorphI.{0} t).down : ℝ) / 2)
  congr 1
  exact actualFlagOneIdCoordinate t

theorem actualBarycentricFlag_swap_regular_reverseRight {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (γ : ActualRegularPath E) :
    barycentricFlagSingular (TopCat.of E) 1 (Equiv.swap 0 1)
      (actualRegularPathAsSingular γ) =
      actualRegularPathAsSingular γ.rightHalf.reverse := by
  apply (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌)).injective
  apply ContinuousMap.ext
  intro t
  change γ.toFun ((barycentricFlag 1 (Equiv.swap 0 1) t).weights 1) =
    γ.toFun ((1 + (1 - (TopCat.stdSimplexHomeomorphI.{0} t).down)) / 2)
  congr 1
  change (barycentricFlag 1 (Equiv.swap 0 1) t).weights 1 =
    (1 + (1 - t.weights 1)) / 2
  rw [actualFlagOneSwapCoordinate]
  ring

theorem actualBarycentricOne_single_regular {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (γ : ActualRegularPath E) :
    singularBarycentricFinsupp (TopCat.of E) 1
      (Finsupp.single (actualRegularPathAsSingular γ) 1) =
      Finsupp.single (actualRegularPathAsSingular γ.leftHalf) 1 -
        Finsupp.single (actualRegularPathAsSingular γ.rightHalf.reverse) 1 := by
  rw [singularBarycentricFinsupp_single]
  have hperm : (Finset.univ : Finset (Equiv.Perm (Fin 2))) =
      {1, Equiv.swap 0 1} := by decide
  rw [hperm, Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [actualBarycentricFlag_id_regular_leftHalf,
    actualBarycentricFlag_swap_regular_reverseRight]
  norm_num
  abel

end CanonicalDimensionTwo
