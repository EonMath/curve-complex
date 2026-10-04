import CurveComplexGenusTwo.Foundations.SingularComparison
import CurveComplexGenusTwo.CWHurewicz.CarrierHomotopy

open CategoryTheory
open scoped Simplicial
open CurveComplexGenusTwo.CWHurewicz

namespace CurveGenusTwo.Filtration
variable {V : Type} [LinearOrder V]

noncomputable def rawSingularSubdivision (K : FiniteComplex V) (n : ℕ) :
    FreeAbelianGroup ((TopCat.toSSet.obj (TopCat.of (geometricRealization K))) _⦋n⦌) →+
    FreeAbelianGroup ((TopCat.toSSet.obj (TopCat.of (geometricRealization K))) _⦋n⦌) :=
  (Finsupp.toFreeAbelianGroup).comp
    ((singularBarycentricFinsupp (TopCat.of (geometricRealization K)) n).toAddMonoidHom.comp
      FreeAbelianGroup.toFinsupp)

noncomputable def rawSingularCarrierHomotopy (K : FiniteComplex V) (n : ℕ) :
    FreeAbelianGroup ((TopCat.toSSet.obj (TopCat.of (geometricRealization K))) _⦋n⦌) →+
    FreeAbelianGroup ((TopCat.toSSet.obj (TopCat.of (geometricRealization K))) _⦋n + 1⦌) :=
  (Finsupp.toFreeAbelianGroup).comp
    ((singularCarrierHomotopy (TopCat.of (geometricRealization K)) n).toAddMonoidHom.comp
      FreeAbelianGroup.toFinsupp)

theorem toFinsupp_singularGeneratorBoundary (K : FiniteComplex V) (n : ℕ)
    (c : FreeAbelianGroup ((TopCat.toSSet.obj
      (TopCat.of (geometricRealization K))) _⦋n + 1⦌)) :
    FreeAbelianGroup.toFinsupp (singularGeneratorBoundary K n c) =
      singularBoundaryFinsupp (TopCat.of (geometricRealization K)) n
        (FreeAbelianGroup.toFinsupp c) := by
  classical
  induction c using FreeAbelianGroup.induction_on with
  | zero => simp
  | of x =>
      simp only [singularGeneratorBoundary_of, map_sum, map_zsmul,
        FreeAbelianGroup.toFinsupp_of, singularBoundaryFinsupp_single]
  | neg x hx => simp only [map_neg, hx]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem rawSingularSubdivision_boundary (K : FiniteComplex V) (n : ℕ)
    (c : FreeAbelianGroup ((TopCat.toSSet.obj
      (TopCat.of (geometricRealization K))) _⦋n + 1⦌)) :
    singularGeneratorBoundary K n (rawSingularSubdivision K (n + 1) c) =
      rawSingularSubdivision K n (singularGeneratorBoundary K n c) := by
  apply (FreeAbelianGroup.equivFinsupp _).injective
  change FreeAbelianGroup.toFinsupp _ = FreeAbelianGroup.toFinsupp _
  rw [toFinsupp_singularGeneratorBoundary]
  simp only [rawSingularSubdivision, AddMonoidHom.comp_apply,
    LinearMap.toAddMonoidHom_coe, FreeAbelianGroup.toFinsupp_toFreeAbelianGroup]
  rw [toFinsupp_singularGeneratorBoundary]
  exact singularBarycentric_boundary_compat _ n _

theorem rawSingularCarrierHomotopy_boundary (K : FiniteComplex V) (n : ℕ)
    (c : FreeAbelianGroup ((TopCat.toSSet.obj
      (TopCat.of (geometricRealization K))) _⦋n + 1⦌)) :
    singularGeneratorBoundary K (n + 1) (rawSingularCarrierHomotopy K (n + 1) c) +
      rawSingularCarrierHomotopy K n (singularGeneratorBoundary K n c) =
        rawSingularSubdivision K (n + 1) c - c := by
  apply (FreeAbelianGroup.equivFinsupp _).injective
  change FreeAbelianGroup.toFinsupp _ = FreeAbelianGroup.toFinsupp _
  simp only [map_add, map_sub, toFinsupp_singularGeneratorBoundary,
    rawSingularCarrierHomotopy, rawSingularSubdivision, AddMonoidHom.comp_apply,
    LinearMap.toAddMonoidHom_coe, FreeAbelianGroup.toFinsupp_toFreeAbelianGroup]
  exact singularCarrierHomotopy_boundary_succ _ n _

theorem rawSingularSubdivision_cycle_difference_boundary (K : FiniteComplex V)
    (n : ℕ) (z : singularPositiveCycles K n) :
    rawSingularSubdivision K (n + 1) z.1 - z.1 ∈
      singularPositiveBoundaries K n := by
  refine ⟨rawSingularCarrierHomotopy K (n + 1) z.1, ?_⟩
  have h := rawSingularCarrierHomotopy_boundary K n z.1
  have hz : singularGeneratorBoundary K n z.1 = 0 := z.2
  simpa only [hz, map_zero, add_zero] using h
end CurveGenusTwo.Filtration
