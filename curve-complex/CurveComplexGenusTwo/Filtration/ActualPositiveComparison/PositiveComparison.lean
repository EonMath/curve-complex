import CurveComplexGenusTwo.Filtration.ApprovedComparisonProducers
import CurveComplexGenusTwo.CWHurewicz.AbsoluteSmallComparison
import CurveComplexGenusTwo.CWHurewicz.SingularRepresentation
import CurveComplexGenusTwo.Filtration.CategoricalSignedE1
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Convexity
open scoped Simplicial
namespace CurveGenusTwo.Filtration
universe u
variable {V : Type u} [LinearOrder V]

@[simp]
theorem positiveHomologyComparison_mk (K : FiniteComplex V) (n : ℕ)
    (c : cycles K ((n + 1 : ℕ) : ℤ)) :
    positiveHomologyComparison K n (QuotientAddGroup.mk c) =
      QuotientAddGroup.mk (positiveCyclesMap K n c) := rfl

theorem positiveHomologyComparison_surjective (K : FiniteComplex V) (n : ℕ) :
    Function.Surjective (positiveHomologyComparison K n) := by
  intro z
  induction z using Quotient.inductionOn with
  | h z =>
    obtain ⟨c, hc⟩ := singularPositiveCycle_lift_mod_boundaries K n z
    refine ⟨QuotientAddGroup.mk c, ?_⟩
    rw [positiveHomologyComparison_mk]
    apply (QuotientAddGroup.eq_iff_sub_mem).mpr
    change (positiveCyclesMap K n c).1 - z.1 ∈ singularPositiveBoundaries K n
    simpa only [neg_sub] using (singularPositiveBoundaries K n).neg_mem hc

theorem positiveHomologyComparison_injective (K : FiniteComplex V) (n : ℕ) :
    Function.Injective (positiveHomologyComparison K n) := by
  apply (positiveHomologyComparison K n).ker_eq_bot_iff.mp
  apply le_antisymm _ bot_le
  intro c hc
  change positiveHomologyComparison K n c = 0 at hc
  change c = 0
  induction c using Quotient.inductionOn with
  | h c =>
    rw [positiveHomologyComparison_mk] at hc
    apply (QuotientAddGroup.eq_zero_iff c).mpr
    change c.1 ∈ boundaries K ((n + 1 : ℕ) : ℤ)
    exact positiveCyclesMap_reflects_boundaries K n c
      ((QuotientAddGroup.eq_zero_iff (positiveCyclesMap K n c)).mp hc)

noncomputable def positiveHomologyComparisonEquiv (K : FiniteComplex V) (n : ℕ) :
    reducedHomology K ((n + 1 : ℕ) : ℤ) ≃+ singularPositiveHomology K n :=
  AddEquiv.ofBijective (positiveHomologyComparison K n)
    ⟨positiveHomologyComparison_injective K n, positiveHomologyComparison_surjective K n⟩
end CurveGenusTwo.Filtration

namespace CurveGenusTwo.Filtration
open CurveComplexGenusTwo.CWHurewicz
universe u
variable {V : Type u} [LinearOrder V]

theorem singularPositiveCycle_bounds_of_reducedHomology_subsingleton
    (K : FiniteComplex V) (n : ℕ)
    [Subsingleton (reducedHomology K ((n + 1 : ℕ) : ℤ))]
    (z : singularPositiveCycles K n) :
    ∃ b, singularGeneratorBoundary K (n + 1) b = z.1 := by
  have hzero : (QuotientAddGroup.mk z : singularPositiveHomology K n) = 0 := by
    obtain ⟨c, hc⟩ := positiveHomologyComparison_surjective K n (QuotientAddGroup.mk z)
    rw [← hc, Subsingleton.elim c 0, map_zero]
  exact (QuotientAddGroup.eq_zero_iff z).mp hzero

/-- Actual positive singular Finsupp cycles bound when the augmented simplicial
homology vanishes. No geometric certificates or additional comparison premises. -/
theorem singularFinsuppCycle_bounds_of_reducedHomology_subsingleton
    (K : FiniteComplex V) (n : ℕ)
    [Subsingleton (reducedHomology K ((n + 1 : ℕ) : ℤ))]
    (z : (TopCat.toSSet.obj (TopCat.of (geometricRealization K))) _⦋n + 1⦌ →₀ ℤ)
    (hz : UniverseSubdivision.singularBoundaryFinsupp (TopCat.of (geometricRealization K)) n z = 0) :
    ∃ b : (TopCat.toSSet.obj (TopCat.of (geometricRealization K))) _⦋n + 2⦌ →₀ ℤ,
      UniverseSubdivision.singularBoundaryFinsupp (TopCat.of (geometricRealization K)) (n + 1) b = z := by
  let c := Finsupp.toFreeAbelianGroup z
  have hc : c ∈ singularPositiveCycles K n := by
    change singularGeneratorBoundary K n c = 0
    apply (FreeAbelianGroup.equivFinsupp _).injective
    change FreeAbelianGroup.toFinsupp _ = FreeAbelianGroup.toFinsupp 0
    rw [UniverseSubdivision.toFinsupp_singularGeneratorBoundary]
    simpa only [c, FreeAbelianGroup.toFinsupp_toFreeAbelianGroup, map_zero] using hz
  obtain ⟨b, hb⟩ := singularPositiveCycle_bounds_of_reducedHomology_subsingleton K n ⟨c, hc⟩
  refine ⟨FreeAbelianGroup.toFinsupp b, ?_⟩
  have h := congrArg FreeAbelianGroup.toFinsupp hb
  rw [UniverseSubdivision.toFinsupp_singularGeneratorBoundary] at h
  simpa only [c, FreeAbelianGroup.toFinsupp_toFreeAbelianGroup] using h
end CurveGenusTwo.Filtration

namespace CurveGenusTwo.Filtration
open CurveComplexGenusTwo.CWHurewicz

theorem universeSingularBoundaryFinsupp_eq (X : TopCat.{0}) (n : ℕ) :
    UniverseSubdivision.singularBoundaryFinsupp X n =
      CurveComplexGenusTwo.CWHurewicz.singularBoundaryFinsupp X n := by
  apply Finsupp.lhom_ext
  intro x b
  have h : Finsupp.single x b = b • Finsupp.single x (1 : ℤ) := by simp
  rw [h, map_smul, map_smul]
  congr 1
  exact (UniverseSubdivision.singularBoundaryFinsupp_single X n x).trans
    (CurveComplexGenusTwo.CWHurewicz.singularBoundaryFinsupp_single X n x).symm

variable {V : Type} [LinearOrder V]

theorem actualSingularCycle_bounds_of_reducedHomology_subsingleton
    (K : FiniteComplex V) (n : ℕ) (hn : 0 < n)
    [Subsingleton (reducedHomology K (n : ℤ))]
    (z : (TopCat.toSSet.obj (TopCat.of (geometricRealization K))) _⦋n⦌ →₀ ℤ)
    (hz : z ∈ absoluteSingularCycles (TopCat.of (geometricRealization K)) n) :
    ∃ b : (TopCat.toSSet.obj (TopCat.of (geometricRealization K))) _⦋n + 1⦌ →₀ ℤ,
      CurveComplexGenusTwo.CWHurewicz.singularBoundaryFinsupp
        (TopCat.of (geometricRealization K)) n b = z := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hz' : UniverseSubdivision.singularBoundaryFinsupp
      (TopCat.of (geometricRealization K)) n z = 0 := by
    rw [universeSingularBoundaryFinsupp_eq]
    exact hz
  obtain ⟨b, hb⟩ := singularFinsuppCycle_bounds_of_reducedHomology_subsingleton K n z hz'
  refine ⟨b, ?_⟩
  simpa only [universeSingularBoundaryFinsupp_eq] using hb
end CurveGenusTwo.Filtration

namespace CurveGenusTwo.Filtration
open CurveComplexGenusTwo.CWHurewicz

noncomputable def rawSingularCyclesFinsuppEquiv
    {V : Type} [LinearOrder V] (K : FiniteComplex V) (n : ℕ) :
    singularPositiveCycles K n ≃+
      (CurveComplexGenusTwo.CWHurewicz.singularBoundaryFinsupp
        (TopCat.of (geometricRealization K)) n).toAddMonoidHom.ker where
  toFun c := ⟨FreeAbelianGroup.toFinsupp c.1, by
    change CurveComplexGenusTwo.CWHurewicz.singularBoundaryFinsupp _ n _ = 0
    have h := congrArg FreeAbelianGroup.toFinsupp c.2
    rw [UniverseSubdivision.toFinsupp_singularGeneratorBoundary,
      universeSingularBoundaryFinsupp_eq] at h
    simpa only [map_zero] using h⟩
  invFun c := ⟨Finsupp.toFreeAbelianGroup c.1, by
    have hc : CurveComplexGenusTwo.CWHurewicz.singularBoundaryFinsupp _ n c.1 = 0 := c.2
    apply (FreeAbelianGroup.equivFinsupp _).injective
    change FreeAbelianGroup.toFinsupp _ = FreeAbelianGroup.toFinsupp 0
    rw [UniverseSubdivision.toFinsupp_singularGeneratorBoundary,
      universeSingularBoundaryFinsupp_eq]
    simpa only [FreeAbelianGroup.toFinsupp_toFreeAbelianGroup, map_zero] using hc⟩
  left_inv c := by apply Subtype.ext; exact Finsupp.toFreeAbelianGroup_toFinsupp c.1
  right_inv c := by apply Subtype.ext; exact FreeAbelianGroup.toFinsupp_toFreeAbelianGroup c.1
  map_add' c d := by apply Subtype.ext; exact map_add _ _ _

noncomputable def rawSingularHomologyFinsuppEquiv
    {V : Type} [LinearOrder V] (K : FiniteComplex V) (n : ℕ) :
    singularPositiveHomology K n ≃+
      ((CurveComplexGenusTwo.CWHurewicz.singularBoundaryFinsupp
        (TopCat.of (geometricRealization K)) n).toAddMonoidHom.ker ⧸
        ((CurveComplexGenusTwo.CWHurewicz.singularBoundaryFinsupp
          (TopCat.of (geometricRealization K)) (n + 1)).toAddMonoidHom.range.comap
          (CurveComplexGenusTwo.CWHurewicz.singularBoundaryFinsupp
            (TopCat.of (geometricRealization K)) n).toAddMonoidHom.ker.subtype)) := by
  apply QuotientAddGroup.congr _ _ (rawSingularCyclesFinsuppEquiv K n)
  ext c
  constructor
  · rintro ⟨z, ⟨b, hb⟩, rfl⟩
    refine ⟨FreeAbelianGroup.toFinsupp b, ?_⟩
    have h := congrArg FreeAbelianGroup.toFinsupp hb
    rw [UniverseSubdivision.toFinsupp_singularGeneratorBoundary,
      universeSingularBoundaryFinsupp_eq] at h
    exact h
  · rintro ⟨b, hb⟩
    refine ⟨(rawSingularCyclesFinsuppEquiv K n).symm c, ?_,
      (rawSingularCyclesFinsuppEquiv K n).apply_symm_apply c⟩
    refine ⟨Finsupp.toFreeAbelianGroup b, ?_⟩
    apply (FreeAbelianGroup.equivFinsupp _).injective
    change FreeAbelianGroup.toFinsupp _ = FreeAbelianGroup.toFinsupp _
    rw [UniverseSubdivision.toFinsupp_singularGeneratorBoundary,
      universeSingularBoundaryFinsupp_eq,
      FreeAbelianGroup.toFinsupp_toFreeAbelianGroup]
    change CurveComplexGenusTwo.CWHurewicz.singularBoundaryFinsupp _ (n + 1) b =
      FreeAbelianGroup.toFinsupp (Finsupp.toFreeAbelianGroup c.1)
    rw [FreeAbelianGroup.toFinsupp_toFreeAbelianGroup]
    exact hb
end CurveGenusTwo.Filtration

namespace CurveGenusTwo.Filtration
open CurveComplexGenusTwo.CWHurewicz

/-- Raw simplex-basis homology is actual categorical integral singular homology. -/
noncomputable def rawSingularHomologyActualIso
    {V : Type} [LinearOrder V] (K : FiniteComplex V) (n : ℕ) :
    ModuleCat.of ℤ (singularPositiveHomology K n) ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of (geometricRealization K)) := by
  let X := TopCat.of (geometricRealization K)
  let C := mvAmbientComplex X
  let S := C.sc' (n + 2) (n + 1) n
  let e := rawSingularHomologyFinsuppEquiv K n
  have he : ModuleCat.of ℤ (singularPositiveHomology K n) ≅
      ModuleCat.of ℤ ((S.g.hom.toAddMonoidHom).ker ⧸
        ((S.f.hom.toAddMonoidHom).range.comap (S.g.hom.toAddMonoidHom).ker.subtype)) := by
    have hg : S.g.hom = singularBoundaryFinsupp X n := by
      change (C.d (n + 1) n).hom = _
      simp only [C, mvAmbientComplex, ChainComplex.of_d, ModuleCat.hom_ofHom]
    have hf : S.f.hom = singularBoundaryFinsupp X (n + 1) := by
      change (C.d ((n + 1) + 1) (n + 1)).hom = _
      simp only [C, mvAmbientComplex, ChainComplex.of_d, ModuleCat.hom_ofHom]
    rw [hg, hf]
    exact e.toIntLinearEquiv.toModuleIso
  exact he ≪≫ (moduleCatHomologyConcreteIso S).symm ≪≫
    (C.homologyIsoSc' (n + 2) (n + 1) n (by simp [ChainComplex.prev])
      (by simp [ChainComplex.next])).symm ≪≫ singularHomologyRepresentation X (n + 1)
end CurveGenusTwo.Filtration

namespace CurveGenusTwo.Filtration
variable {V : Type} [LinearOrder V]

/-- Genuine comparison in every positive degree; geometricRealization is the
canonical nonempty-face weak realization of the augmented complex. -/
theorem augmented_singular_comparison_positive_canonical
    (K : FiniteComplex V) (n : ℕ) (hn : 0 < n) :
    Nonempty (ModuleCat.of ℤ (reducedHomology K (n : ℤ)) ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of (geometricRealization K))) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact ⟨(positiveHomologyComparisonEquiv K n).toIntLinearEquiv.toModuleIso ≪≫
    rawSingularHomologyActualIso K n⟩

#print axioms positiveHomologyComparisonEquiv
#print axioms actualSingularCycle_bounds_of_reducedHomology_subsingleton
#print axioms augmented_singular_comparison_positive_canonical
end CurveGenusTwo.Filtration
