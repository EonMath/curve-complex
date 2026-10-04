import CurveComplexGenusTwo.CWHurewicz.PairHomotopyInvariance

namespace CurveComplexGenusTwo.CWHurewicz

open CategoryTheory CategoryTheory.Limits Topology

private noncomputable abbrev actualChainFunctor :=
  (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)

set_option backward.isDefEq.respectTransparency false in
theorem actual_pairRelativeChainMap_zero_of_range_in_subspace
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y))
    (h : ∀ x ∈ A, f x ∈ B) (hrange : ∀ x, f x ∈ B) :
    pairRelativeChainMap A B f h = 0 := by
  let lift : TopCat.of X ⟶ TopCat.of B :=
    TopCat.ofHom ⟨fun x => ⟨f x, hrange x⟩, f.continuous.subtype_mk _⟩
  have hfactor : TopCat.ofHom f = lift ≫ pairInclusion Y B := by
    ext x
    rfl
  apply (cancel_epi (cokernel.π (actualChainFunctor.map (pairInclusion X A)))).mp
  rw [pairRelativeChainMap_π, hfactor, Functor.map_comp, Category.assoc,
    cokernel.condition, comp_zero]
  simp


theorem actual_pairRelativeHomologyMap_zero_of_range_in_subspace
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y))
    (h : ∀ x ∈ A, f x ∈ B) (hrange : ∀ x, f x ∈ B) (n : ℕ) :
    pairRelativeHomologyMap A B f h n = 0 := by
  change HomologicalComplex.homologyMap (pairRelativeChainMap A B f h) n = 0
  rw [actual_pairRelativeChainMap_zero_of_range_in_subspace A B f h hrange,
    HomologicalComplex.homologyMap_zero]


end CurveComplexGenusTwo.CWHurewicz
