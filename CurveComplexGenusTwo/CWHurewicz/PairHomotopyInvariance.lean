import CurveComplexGenusTwo.CWHurewicz.PairNaturality
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

namespace CurveComplexGenusTwo.CWHurewicz

open CategoryTheory CategoryTheory.Limits Topology MonoidalCategory
open scoped Simplicial

/-- Restriction of a pair homotopy to the chosen subspaces. -/
private def pairHomotopyOnSubspace
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f g : C(X, Y))
    (hf : ∀ x ∈ A, f x ∈ B) (hg : ∀ x ∈ A, g x ∈ B)
    (H : ContinuousMap.Homotopy f g)
    (hH : ∀ (t : unitInterval) (x : X), x ∈ A → H (t, x) ∈ B) :
    TopCat.Homotopy (pairMapOnSubspace A B f hf) (pairMapOnSubspace A B g hg) where
  toContinuousMap := ⟨fun p => ⟨H (p.1, p.2.val), hH p.1 p.2.val p.2.property⟩, by
    fun_prop⟩
  map_zero_left x := by
    apply Subtype.ext
    exact H.map_zero_left x.val
  map_one_left x := by
    apply Subtype.ext
    exact H.map_one_left x.val

private noncomputable abbrev pairChainFunctor :=
  (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)

/-- The absolute prism homotopy on the ambient spaces. -/
private noncomputable def pairAmbientChainHomotopy
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f g : C(X, Y)) (H : ContinuousMap.Homotopy f g) :
    _root_.Homotopy (pairChainFunctor.map (TopCat.ofHom f))
      (pairChainFunctor.map (TopCat.ofHom g)) :=
  TopCat.Homotopy.singularChainComplexFunctorObjMap H (ModuleCat.of ℤ ℤ)

/-- The same prism homotopy on the subspace pair. -/
private noncomputable def pairSubspaceChainHomotopy
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f g : C(X, Y))
    (hf : ∀ x ∈ A, f x ∈ B) (hg : ∀ x ∈ A, g x ∈ B)
    (H : ContinuousMap.Homotopy f g)
    (hH : ∀ (t : unitInterval) (x : X), x ∈ A → H (t, x) ∈ B) :
    _root_.Homotopy (pairChainFunctor.map (pairMapOnSubspace A B f hf))
      (pairChainFunctor.map (pairMapOnSubspace A B g hg)) :=
  TopCat.Homotopy.singularChainComplexFunctorObjMap
    (pairHomotopyOnSubspace A B f g hf hg H hH) (ModuleCat.of ℤ ℤ)

private theorem pairHomotopy_h_square
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f g : C(X, Y))
    (hf : ∀ x ∈ A, f x ∈ B) (hg : ∀ x ∈ A, g x ∈ B)
    (H : ContinuousMap.Homotopy f g)
    (hH : ∀ (t : unitInterval) (x : X), x ∈ A → H (t, x) ∈ B) :
    pairInclusion X A ▷ TopCat.I ≫ TopCat.Homotopy.h H =
      TopCat.Homotopy.h (pairHomotopyOnSubspace A B f g hf hg H hH) ≫
        pairInclusion Y B := by
  ext p
  rfl

private theorem pairHomotopy_toSSet_h_square
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f g : C(X, Y))
    (hf : ∀ x ∈ A, f x ∈ B) (hg : ∀ x ∈ A, g x ∈ B)
    (H : ContinuousMap.Homotopy f g)
    (hH : ∀ (t : unitInterval) (x : X), x ∈ A → H (t, x) ∈ B) :
    (TopCat.toSSet.map (pairInclusion X A) ▷ Δ[1]) ≫
        (TopCat.Homotopy.toSSet H).h =
      (TopCat.Homotopy.toSSet (pairHomotopyOnSubspace A B f g hf hg H hH)).h ≫
        TopCat.toSSet.map (pairInclusion Y B) := by
  simp only [TopCat.Homotopy.toSSet]
  rw [Category.assoc, ← MonoidalCategory.whisker_exchange_assoc]
  rw [Functor.LaxMonoidal.μ_natural_left_assoc]
  simp only [← Functor.map_comp]
  rw [pairHomotopy_h_square A B f g hf hg H hH]
  simp only [Functor.map_comp, Category.assoc]

private theorem pairHomotopy_simplicial_h_square
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f g : C(X, Y))
    (hf : ∀ x ∈ A, f x ∈ B) (hg : ∀ x ∈ A, g x ∈ B)
    (H : ContinuousMap.Homotopy f g)
    (hH : ∀ (t : unitInterval) (x : X), x ∈ A → H (t, x) ∈ B)
    (n : ℕ) (k : Fin (n + 1)) :
    (TopCat.toSSet.map (pairInclusion X A)).app (Opposite.op ⦋n⦌) ≫
        (TopCat.Homotopy.toSSet H).toSimplicialObjectHomotopy.h k =
      (TopCat.Homotopy.toSSet
        (pairHomotopyOnSubspace A B f g hf hg H hH)).toSimplicialObjectHomotopy.h k ≫
        (TopCat.toSSet.map (pairInclusion Y B)).app (Opposite.op ⦋n + 1⦌) := by
  ext x
  dsimp [SSet.Homotopy.toSimplicialObjectHomotopy]
  have hy : SSet.yonedaEquiv.symm
        ((TopCat.toSSet.map (pairInclusion X A)).app (Opposite.op ⦋n⦌) x) =
      SSet.yonedaEquiv.symm x ≫ TopCat.toSSet.map (pairInclusion X A) := by
    apply SSet.yonedaEquiv.injective
    simp [SSet.yonedaEquiv_comp]
  rw [hy]
  have hs := pairHomotopy_toSSet_h_square A B f g hf hg H hH
  have hs' := congrArg (fun q => (q.app (Opposite.op ⦋n + 1⦌))
    (((SSet.yonedaEquiv.symm x ▷ Δ[1]).app (Opposite.op ⦋n + 1⦌))
      (SSet.prodStdSimplex₁.nonDegenerateEquiv k).1)) hs
  convert hs' using 1 <;> rfl

set_option backward.isDefEq.respectTransparency false in
private theorem pairHomotopy_chain_h_square
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f g : C(X, Y))
    (hf : ∀ x ∈ A, f x ∈ B) (hg : ∀ x ∈ A, g x ∈ B)
    (H : ContinuousMap.Homotopy f g)
    (hH : ∀ (t : unitInterval) (x : X), x ∈ A → H (t, x) ∈ B)
    (i j : ℕ) :
    (pairChainFunctor.map (pairInclusion X A)).f i ≫
        (pairAmbientChainHomotopy f g H).hom i j =
      (pairSubspaceChainHomotopy A B f g hf hg H hH).hom i j ≫
        (pairChainFunctor.map (pairInclusion Y B)).f j := by
  by_cases hij : i + 1 = j
  · subst j
    change (SSet.chainComplexMap (TopCat.toSSet.map (pairInclusion X A))
        (ModuleCat.of ℤ ℤ)).f i ≫ (pairAmbientChainHomotopy f g H).hom i (i + 1) =
      (pairSubspaceChainHomotopy A B f g hf hg H hH).hom i (i + 1) ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (pairInclusion Y B))
          (ModuleCat.of ℤ ℤ)).f (i + 1)
    simp only [pairAmbientChainHomotopy, pairSubspaceChainHomotopy,
      TopCat.Homotopy.singularChainComplexFunctorObjMap,
      SSet.Homotopy.chainComplexMap,
      CategoryTheory.SimplicialObject.Homotopy.sSetChainComplexMap,
      CategoryTheory.SimplicialObject.Homotopy.toChainHomotopy,
      CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom_eq]
    simp only [Preadditive.comp_neg, Preadditive.neg_comp,
      Preadditive.comp_sum, Preadditive.sum_comp,
      Preadditive.comp_zsmul, Preadditive.zsmul_comp]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    change (sigmaConst.obj (ModuleCat.of ℤ ℤ)).map
        ((TopCat.toSSet.map (pairInclusion X A)).app (Opposite.op ⦋i⦌)) ≫
        (sigmaConst.obj (ModuleCat.of ℤ ℤ)).map
          ((TopCat.Homotopy.toSSet H).toSimplicialObjectHomotopy.h k) =
      (sigmaConst.obj (ModuleCat.of ℤ ℤ)).map
          ((TopCat.Homotopy.toSSet
            (pairHomotopyOnSubspace A B f g hf hg H hH)).toSimplicialObjectHomotopy.h k) ≫
        (sigmaConst.obj (ModuleCat.of ℤ ℤ)).map
          ((TopCat.toSSet.map (pairInclusion Y B)).app (Opposite.op ⦋i + 1⦌))
    rw [← Functor.map_comp, ← Functor.map_comp,
      pairHomotopy_simplicial_h_square A B f g hf hg H hH i k]
  · simp [pairAmbientChainHomotopy, pairSubspaceChainHomotopy,
      TopCat.Homotopy.singularChainComplexFunctorObjMap,
      SSet.Homotopy.chainComplexMap,
      CategoryTheory.SimplicialObject.Homotopy.sSetChainComplexMap,
      CategoryTheory.SimplicialObject.Homotopy.toChainHomotopy,
      CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom_eq_zero, hij]

private noncomputable def pairRelativeCokernelIsColimit
    (X : Type) [TopologicalSpace X] (A : Set X) (i : ℕ) :
    IsColimit (CokernelCofork.ofπ
      ((cokernel.π (pairChainFunctor.map (pairInclusion X A))).f i)
      (by
        rw [← HomologicalComplex.comp_f, cokernel.condition]
        rfl)) := by
  convert CokernelCofork.mapIsColimit
    (CokernelCofork.ofπ (cokernel.π (pairChainFunctor.map (pairInclusion X A)))
      (cokernel.condition _))
    (cokernelIsCokernel (pairChainFunctor.map (pairInclusion X A)))
    (HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) i) using 1 <;> rfl

set_option backward.isDefEq.respectTransparency false in
private theorem pairHomotopy_component_condition
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f g : C(X, Y))
    (hf : ∀ x ∈ A, f x ∈ B) (hg : ∀ x ∈ A, g x ∈ B)
    (H : ContinuousMap.Homotopy f g)
    (hH : ∀ (t : unitInterval) (x : X), x ∈ A → H (t, x) ∈ B)
    (i j : ℕ) :
    (pairChainFunctor.map (pairInclusion X A)).f i ≫
        ((pairAmbientChainHomotopy f g H).hom i j ≫
          (cokernel.π (pairChainFunctor.map (pairInclusion Y B))).f j) = 0 := by
  rw [← Category.assoc, pairHomotopy_chain_h_square A B f g hf hg H hH i j,
    Category.assoc, ← HomologicalComplex.comp_f, cokernel.condition]
  simp

private noncomputable def pairRelativeHomotopyComponent
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f g : C(X, Y))
    (hf : ∀ x ∈ A, f x ∈ B) (hg : ∀ x ∈ A, g x ∈ B)
    (H : ContinuousMap.Homotopy f g)
    (hH : ∀ (t : unitInterval) (x : X), x ∈ A → H (t, x) ∈ B)
    (i j : ℕ) :
    (relativeSingularChains X A).X i ⟶ (relativeSingularChains Y B).X j :=
  (pairRelativeCokernelIsColimit X A i).desc
    (CokernelCofork.ofπ
      ((pairAmbientChainHomotopy f g H).hom i j ≫
        (cokernel.π (pairChainFunctor.map (pairInclusion Y B))).f j)
      (pairHomotopy_component_condition A B f g hf hg H hH i j))

set_option backward.isDefEq.respectTransparency false in
private theorem pairRelativeHomotopyComponent_fac
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f g : C(X, Y))
    (hf : ∀ x ∈ A, f x ∈ B) (hg : ∀ x ∈ A, g x ∈ B)
    (H : ContinuousMap.Homotopy f g)
    (hH : ∀ (t : unitInterval) (x : X), x ∈ A → H (t, x) ∈ B)
    (i j : ℕ) :
    (cokernel.π (pairChainFunctor.map (pairInclusion X A))).f i ≫
        pairRelativeHomotopyComponent A B f g hf hg H hH i j =
      (pairAmbientChainHomotopy f g H).hom i j ≫
        (cokernel.π (pairChainFunctor.map (pairInclusion Y B))).f j := by
  exact (pairRelativeCokernelIsColimit X A i).fac
    (CokernelCofork.ofπ _ (pairHomotopy_component_condition A B f g hf hg H hH i j))
    WalkingParallelPair.one

set_option backward.isDefEq.respectTransparency false in
private noncomputable def pairRelativeChainHomotopy
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f g : C(X, Y))
    (hf : ∀ x ∈ A, f x ∈ B) (hg : ∀ x ∈ A, g x ∈ B)
    (H : ContinuousMap.Homotopy f g)
    (hH : ∀ (t : unitInterval) (x : X), x ∈ A → H (t, x) ∈ B) :
    _root_.Homotopy (pairRelativeChainMap A B f hf)
      (pairRelativeChainMap A B g hg) where
  hom := pairRelativeHomotopyComponent A B f g hf hg H hH
  zero i j hij := by
    let qX := cokernel.π (pairChainFunctor.map (pairInclusion X A))
    have : Epi (qX.f i) := by
      change Epi ((HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) i).map qX)
      infer_instance
    apply (cancel_epi (qX.f i)).1
    rw [pairRelativeHomotopyComponent_fac]
    change _ = qX.f i ≫ 0
    rw [(pairAmbientChainHomotopy f g H).zero i j hij]
    simp
  comm i := by
    let qX := cokernel.π (pairChainFunctor.map (pairInclusion X A))
    let qY := cokernel.π (pairChainFunctor.map (pairInclusion Y B))
    have hfamily :
        (fun a b => qX.f a ≫ pairRelativeHomotopyComponent A B f g hf hg H hH a b) =
          (fun a b => (pairAmbientChainHomotopy f g H).hom a b ≫ qY.f b) := by
      funext a b
      exact pairRelativeHomotopyComponent_fac A B f g hf hg H hH a b
    have : Epi (qX.f i) := by
      change Epi ((HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) i).map qX)
      infer_instance
    apply (cancel_epi (qX.f i)).1
    simp only [Preadditive.comp_add]
    erw [← dNext_comp_left qX _ i, ← prevD_comp_left qX _ i]
    rw [hfamily, dNext_comp_right, prevD_comp_right]
    have hfπ : qX.f i ≫ (pairRelativeChainMap A B f hf).f i =
        (pairChainFunctor.map (TopCat.ofHom f)).f i ≫ qY.f i := by
      exact congrArg (fun t => t.f i) (pairRelativeChainMap_π A B f hf)
    have hgπ : qX.f i ≫ (pairRelativeChainMap A B g hg).f i =
        (pairChainFunctor.map (TopCat.ofHom g)).f i ≫ qY.f i := by
      exact congrArg (fun t => t.f i) (pairRelativeChainMap_π A B g hg)
    rw [hfπ, hgπ]
    simp only [← Preadditive.add_comp]
    rw [← (pairAmbientChainHomotopy f g H).comm i]

/-- A homotopy through maps of pairs induces the same map on the canonical
relative integral singular homology quotient in every degree. -/
theorem pairRelativeHomologyMap_homotopy
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f g : C(X, Y))
    (hf : ∀ x ∈ A, f x ∈ B) (hg : ∀ x ∈ A, g x ∈ B)
    (H : ContinuousMap.Homotopy f g)
    (hH : ∀ (t : unitInterval) (x : X), x ∈ A → H (t, x) ∈ B)
    (n : ℕ) :
    pairRelativeHomologyMap A B f hf n =
      pairRelativeHomologyMap A B g hg n := by
  exact (pairRelativeChainHomotopy A B f g hf hg H hH).homologyMap_eq n

end CurveComplexGenusTwo.CWHurewicz
