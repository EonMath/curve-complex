import CurveComplexGenusTwo.CWHurewicz.PairNaturality
import CurveComplexGenusTwo.CWHurewicz.RelativeExactClean
import Mathlib.Algebra.Homology.HomologySequenceLemmas

namespace CurveComplexGenusTwo.CWHurewicz

open CategoryTheory CategoryTheory.Limits Topology

private noncomputable abbrev F :=
  (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)

private noncomputable abbrev G (n : ℕ) :=
  (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
    (ModuleCat.of ℤ ℤ)

private instance inclusionMono {X : Type} [TopologicalSpace X] (A : Set X) :
    Mono (pairInclusion X A) :=
  (TopCat.mono_iff_injective _).mpr Subtype.val_injective

private instance chainInclusionMono {X : Type} [TopologicalSpace X] (A : Set X) :
    Mono (F.map (pairInclusion X A)) :=
  F.map_mono _

private noncomputable def pairChainShortComplex (X : Type) [TopologicalSpace X]
    (A : Set X) : ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  ShortComplex.mk (F.map (pairInclusion X A))
    (cokernel.π (F.map (pairInclusion X A)))
    (cokernel.condition _)

private lemma pairChainShortExact (X : Type) [TopologicalSpace X]
    (A : Set X) : (pairChainShortComplex X A).ShortExact where
  exact := ShortComplex.exact_cokernel _
  mono_f := by
    dsimp [pairChainShortComplex]
    infer_instance
  epi_g := by
    dsimp [pairChainShortComplex]
    infer_instance

/-- A map of pairs induces a morphism of the short exact chain sequences
`C_*(A) -> C_*(X) -> C_*(X,A)`. -/
noncomputable def pairChainShortComplexMap
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y))
    (h : ∀ x ∈ A, f x ∈ B) :
    pairChainShortComplex X A ⟶ pairChainShortComplex Y B where
  τ₁ := F.map (pairMapOnSubspace A B f h)
  τ₂ := F.map (TopCat.ofHom f)
  τ₃ := pairRelativeChainMap A B f h
  comm₁₂ := by
    dsimp [pairChainShortComplex]
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg F.map (pairMap_square A B f h).symm
  comm₂₃ := by
    dsimp [pairChainShortComplex]
    exact (pairRelativeChainMap_π A B f h).symm

/-- This short exact model has the same connecting morphism as the existing LES. -/
theorem pairConnecting_eq_relativeConnecting
    (X : Type) [TopologicalSpace X] (A : Set X) (n : ℕ) :
    (pairChainShortExact X A).δ (n + 1) n (by simp) =
      relativeConnecting X A n := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The connecting map in relative singular homology is natural for maps of pairs. -/
theorem relativeConnecting_natural
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y))
    (h : ∀ x ∈ A, f x ∈ B) (n : ℕ) :
    relativeConnecting X A n ≫ (G n).map (pairMapOnSubspace A B f h) =
      pairRelativeHomologyMap A B f h (n + 1) ≫
        relativeConnecting Y B n := by
  have hnat := HomologicalComplex.HomologySequence.δ_naturality
    (pairChainShortComplexMap A B f h)
    (pairChainShortExact X A) (pairChainShortExact Y B)
    (n + 1) n (by simp)
  rw [pairConnecting_eq_relativeConnecting,
    pairConnecting_eq_relativeConnecting] at hnat
  exact hnat

#print axioms pairChainShortComplexMap
#print axioms pairConnecting_eq_relativeConnecting
#print axioms relativeConnecting_natural

end CurveComplexGenusTwo.CWHurewicz
