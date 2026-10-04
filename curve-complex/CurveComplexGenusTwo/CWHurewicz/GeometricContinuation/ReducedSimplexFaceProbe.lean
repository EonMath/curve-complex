import CurveComplexGenusTwo.CWHurewicz.SingularRepresentation
open CategoryTheory Convexity
open scoped Simplicial
noncomputable section
namespace CurveComplexGenusTwo.CWHurewicz
theorem reducedSimplex_face {Y : Type} [TopologicalSpace Y] (n : ℕ) (y : Y)
    (q : C(StdSimplex ℝ (Fin (n + 2)), Y))
    (hq : ∀ t, ¬(∀ i, 0 < t.weights i) → q t = y)
    (i : Fin (n + 2)) :
    (TopCat.toSSet.obj (TopCat.of Y)).δ i
      ((TopCat.toSSetObjEquiv (TopCat.of Y) (.op ⦋n + 1⦌)).symm q) =
    (TopCat.toSSetObjEquiv (TopCat.of Y) (.op ⦋n⦌)).symm
      (ContinuousMap.const _ y) := by
  apply (TopCat.toSSetObjEquiv (TopCat.of Y) (.op ⦋n⦌)).injective
  ext t
  simp only [Equiv.apply_symm_apply,
    ContinuousMap.const_apply]
  change q (t.map i.succAbove) = y
  apply hq
  intro h
  have hz : (t.map i.succAbove).weights i = 0 := by
    rw [StdSimplex.weights_map]
    exact Finsupp.mapDomain_of_notMem_range _ _ (by
      rintro ⟨j, hj⟩
      exact Fin.succAbove_ne i j hj)
  simpa only [hz, lt_self_iff_false] using h i
theorem reducedSimplex_boundary {Y : Type} [TopologicalSpace Y] (n : ℕ) (y : Y)
    (q : C(StdSimplex ℝ (Fin (n + 2)), Y))
    (hq : ∀ t, ¬(∀ i, 0 < t.weights i) → q t = y) :
    singularBoundaryFinsupp (TopCat.of Y) n
      (Finsupp.single ((TopCat.toSSetObjEquiv (TopCat.of Y) (.op ⦋n + 1⦌)).symm q) 1 -
       Finsupp.single ((TopCat.toSSetObjEquiv (TopCat.of Y) (.op ⦋n + 1⦌)).symm
         (ContinuousMap.const _ y)) 1) = 0 := by
  rw [map_sub, singularBoundaryFinsupp_single, singularBoundaryFinsupp_single]
  apply sub_eq_zero.mpr
  apply Finset.sum_congr rfl
  intro i _
  rw [reducedSimplex_face n y q hq i,
    reducedSimplex_face n y (ContinuousMap.const _ y) (by intros; rfl) i]
theorem reducedSimplex_cycle {Y : Type} [TopologicalSpace Y] (n : ℕ) (y : Y)
    (q : C(StdSimplex ℝ (Fin (n + 2)), Y))
    (hq : ∀ t, ¬(∀ i, 0 < t.weights i) → q t = y) :
    ∃ z : (singularChains (TopCat.of Y)).cycles (n + 1),
      (singularChains (TopCat.of Y)).iCycles (n + 1) z =
      (singularChainsFinsuppIso (TopCat.of Y) (n + 1)).inv
        (Finsupp.single ((TopCat.toSSetObjEquiv (TopCat.of Y) (.op ⦋n + 1⦌)).symm q) 1 -
         Finsupp.single ((TopCat.toSSetObjEquiv (TopCat.of Y) (.op ⦋n + 1⦌)).symm
           (ContinuousMap.const _ y)) 1) := by
  let K := singularChains (TopCat.of Y)
  let c : (TopCat.toSSet.obj (TopCat.of Y)) _⦋n + 1⦌ →₀ ℤ := Finsupp.single ((TopCat.toSSetObjEquiv (TopCat.of Y) (.op ⦋n + 1⦌)).symm q) 1 -
    Finsupp.single ((TopCat.toSSetObjEquiv (TopCat.of Y) (.op ⦋n + 1⦌)).symm
      (ContinuousMap.const _ y)) 1
  let a := (singularChainsFinsuppIso (TopCat.of Y) (n + 1)).inv c
  have ha : K.d (n + 1) n a = 0 := by
    have hb := congrArg (fun f => f c) (singularRepresentation_boundary (TopCat.of Y) n)
    change (singularChainsFinsuppIso (TopCat.of Y) n).inv
      (singularBoundaryFinsupp (TopCat.of Y) n c) = K.d (n + 1) n a at hb
    rw [show singularBoundaryFinsupp (TopCat.of Y) n c = 0 from
      reducedSimplex_boundary n y q hq, map_zero] at hb
    exact hb.symm
  let v : LinearMap.ker (K.sc (n + 1)).g.hom := ⟨a, by
    change K.d (n + 1) ((ComplexShape.down ℕ).next (n + 1)) a = 0
    rw [ComplexShape.next_eq' (ComplexShape.down ℕ) (by rfl :
      (ComplexShape.down ℕ).Rel (n + 1) n)]
    exact ha⟩
  refine ⟨(K.sc (n + 1)).moduleCatCyclesIso.inv v, ?_⟩
  exact congrArg (fun f => f v) ((K.sc (n + 1)).moduleCatCyclesIso_inv_iCycles)
theorem reducedSimplex_push {Y X : Type} [TopologicalSpace Y] [TopologicalSpace X]
    (n : ℕ) (y : Y) (f : C(Y, X))
    (q : C(StdSimplex ℝ (Fin (n + 1)), Y)) :
    (actualSingularFunctor.map (TopCat.ofHom f)).f n
      ((singularChainsFinsuppIso (TopCat.of Y) n).inv
        (Finsupp.single ((TopCat.toSSetObjEquiv (TopCat.of Y) (.op ⦋n⦌)).symm q) 1 -
         Finsupp.single ((TopCat.toSSetObjEquiv (TopCat.of Y) (.op ⦋n⦌)).symm
           (ContinuousMap.const _ y)) 1)) =
    (singularChainsFinsuppIso (TopCat.of X) n).inv
      (Finsupp.single ((TopCat.toSSetObjEquiv (TopCat.of X) (.op ⦋n⦌)).symm (f.comp q)) 1 -
       Finsupp.single ((TopCat.toSSetObjEquiv (TopCat.of X) (.op ⦋n⦌)).symm
         (ContinuousMap.const _ (f y))) 1) := by
  rw [singularRepresentation_basis_naturality]
  congr 1
  simp only [map_sub, singularFinsuppPush, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single]
  have hn (q : C(StdSimplex ℝ (Fin (n + 1)), Y)) :
      (TopCat.toSSet.map (TopCat.ofHom f)).app (.op ⦋n⦌)
        ((TopCat.toSSetObjEquiv (TopCat.of Y) (.op ⦋n⦌)).symm q) =
      (TopCat.toSSetObjEquiv (TopCat.of X) (.op ⦋n⦌)).symm (f.comp q) := by
    apply (TopCat.toSSetObjEquiv (TopCat.of X) (.op ⦋n⦌)).injective
    ext t
    rfl
  rw [hn q, hn (ContinuousMap.const _ y)]
  rfl
theorem reducedSimplex_sum {α β : Type} (c : α →₀ ℤ) (u : α → β) (b : β) :
    Finsupp.mapDomain u c - (∑ a ∈ c.support, c a) • Finsupp.single b 1 =
      ∑ a ∈ c.support, c a • (Finsupp.single (u a) 1 - Finsupp.single b 1) := by
  classical
  simp only [smul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_smul]
  congr 1
  calc
    Finsupp.mapDomain u c = Finsupp.mapDomain u (c.sum Finsupp.single) :=
      congrArg _ (Finsupp.sum_single c).symm
    _ = c.sum (fun a r => Finsupp.single (u a) r) := by
      rw [Finsupp.mapDomain_sum]
      simp only [Finsupp.mapDomain_single]
    _ = _ := by simp only [Finsupp.sum, Finsupp.smul_single, smul_eq_mul, mul_one]
end CurveComplexGenusTwo.CWHurewicz
