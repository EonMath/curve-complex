import CurveComplexGenusTwo.Filtration.StarSmallSSetProbe
import Mathlib.Algebra.FreeAbelianGroup.Finsupp

open CategoryTheory
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
namespace CurveGenusTwo.Filtration
universe u
variable {V : Type u} [LinearOrder V]

noncomputable def starSmallChainInclusion (K : FiniteComplex V) (n : ℕ) :
    FreeAbelianGroup (StarSmallSimplex K n) →+
      FreeAbelianGroup ((TopCat.toSSet.obj (TopCat.of (geometricRealization K))) _⦋n⦌) :=
  FreeAbelianGroup.map Subtype.val

theorem starSmallChainInclusion_injective (K : FiniteComplex V) (n : ℕ) :
    Function.Injective (starSmallChainInclusion K n) := by
  classical
  let r : FreeAbelianGroup ((TopCat.toSSet.obj (TopCat.of (geometricRealization K))) _⦋n⦌) →+ FreeAbelianGroup (StarSmallSimplex K n) := FreeAbelianGroup.lift fun s =>
    if hs : ∃ v : ActiveVertex K, singularSimplexImage K n s ⊆
      CurveComplex.openVertexStar (geometricComplex K) v then
      FreeAbelianGroup.of (⟨s, hs⟩ : StarSmallSimplex K n) else 0
  have hr : r.comp (starSmallChainInclusion K n) = AddMonoidHom.id _ := by
    apply FreeAbelianGroup.lift_ext
    intro s
    simp [r, starSmallChainInclusion, s.2]
  intro a b h
  have := congrArg r h
  simpa only [← AddMonoidHom.comp_apply, hr, AddMonoidHom.id_apply] using this

theorem starSmallChainInclusion_boundary (K : FiniteComplex V) (n : ℕ)
    (c : FreeAbelianGroup (StarSmallSimplex K (n + 1))) :
    starSmallChainInclusion K n (starSmallBoundary K n c) =
      singularGeneratorBoundary K n (starSmallChainInclusion K (n + 1) c) := by
  have h : (starSmallChainInclusion K n).comp (starSmallBoundary K n) =
      (singularGeneratorBoundary K n).comp (starSmallChainInclusion K (n + 1)) := by
    apply FreeAbelianGroup.lift_ext
    intro s
    simp only [AddMonoidHom.comp_apply, starSmallBoundary_of, map_sum, map_zsmul,
      starSmallChainInclusion, FreeAbelianGroup.map_of_apply, singularGeneratorBoundary_of]
    rfl
  exact DFunLike.congr_fun h c

theorem exists_starSmallChain_lift (K : FiniteComplex V) (n : ℕ)
    (z : FreeAbelianGroup ((TopCat.toSSet.obj (TopCat.of (geometricRealization K))) _⦋n⦌))
    (hz : ∀ s ∈ (FreeAbelianGroup.toFinsupp z).support,
      ∃ v : ActiveVertex K, singularSimplexImage K n s ⊆
        CurveComplex.openVertexStar (geometricComplex K) v) :
    ∃ c : FreeAbelianGroup (StarSmallSimplex K n), starSmallChainInclusion K n c = z := by
  classical
  have hmem : z ∈ (starSmallChainInclusion K n).range := by
    rw [FreeAbelianGroup.eq_sum_support_coeff_smul_of z]
    apply AddSubgroup.sum_mem
    intro s hs
    apply AddSubgroup.zsmul_mem
    exact ⟨FreeAbelianGroup.of ⟨s, hz s hs⟩, rfl⟩
  exact hmem

theorem exists_starSmallCycle_lift (K : FiniteComplex V) (n : ℕ)
    (z : singularPositiveCycles K n)
    (hz : ∀ s ∈ (FreeAbelianGroup.toFinsupp z.1).support,
      ∃ v : ActiveVertex K, singularSimplexImage K (n + 1) s ⊆
        CurveComplex.openVertexStar (geometricComplex K) v) :
    ∃ c : FreeAbelianGroup (StarSmallSimplex K (n + 1)),
      starSmallBoundary K n c = 0 ∧ starSmallChainInclusion K (n + 1) c = z.1 := by
  obtain ⟨c, hc⟩ := exists_starSmallChain_lift K (n + 1) z.1 hz
  refine ⟨c, ?_, hc⟩
  apply starSmallChainInclusion_injective K n
  rw [starSmallChainInclusion_boundary, hc, map_zero]
  exact z.2

#print axioms starSmallChainInclusion_injective
#print axioms starSmallChainInclusion_boundary
#print axioms exists_starSmallCycle_lift
end CurveGenusTwo.Filtration
