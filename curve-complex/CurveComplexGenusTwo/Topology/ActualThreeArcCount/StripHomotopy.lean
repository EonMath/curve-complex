import Mathlib
open Set Topology ContinuousMap
noncomputable section
namespace CurveComplexGenusTwo.SourceTopology.ThreeArcCut


/-- Homotopies on the two open-and-closed summands assemble continuously. -/
def sumDomainHomotopy
    {A B C : Type} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    {f₀ f₁ : C(A, C)} {g₀ g₁ : C(B, C)}
    (F : f₀.Homotopy f₁) (G : g₀.Homotopy g₁) :
    (⟨Sum.elim f₀ g₀, f₀.continuous.sumElim g₀.continuous⟩ : C(A ⊕ B, C)).Homotopy
      ⟨Sum.elim f₁ g₁, f₁.continuous.sumElim g₁.continuous⟩ where
  toFun := fun p => Sum.elim (fun a => F (p.1, a)) (fun b => G (p.1, b)) p.2
  continuous_toFun := by
    convert (F.continuous.sumElim G.continuous).comp Homeomorph.prodSumDistrib.continuous using 1
    ext ⟨t, x⟩
    cases x <;> rfl
  map_zero_left := by intro x; cases x <;> simp
  map_one_left := by intro x; cases x <;> simp

def sumHomotopyEquiv
    {A B C D : Type} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace C] [TopologicalSpace D]
    (e : A ≃ₕ C) (f : B ≃ₕ D) : (A ⊕ B) ≃ₕ (C ⊕ D) where
  toFun := ⟨Sum.map e.toFun f.toFun, e.toFun.continuous.sumMap f.toFun.continuous⟩
  invFun := ⟨Sum.map e.invFun f.invFun, e.invFun.continuous.sumMap f.invFun.continuous⟩
  left_inv := by
    have F := (ContinuousMap.Homotopy.refl
      (⟨Sum.inl, continuous_inl⟩ : C(A, A ⊕ B))).comp e.left_inv.some
    have G := (ContinuousMap.Homotopy.refl
      (⟨Sum.inr, continuous_inr⟩ : C(B, A ⊕ B))).comp f.left_inv.some
    have hh := (show ContinuousMap.Homotopic _ _ from ⟨sumDomainHomotopy F G⟩)
    convert hh using 1 <;> ext x <;> cases x <;> rfl
  right_inv := by
    have F := (ContinuousMap.Homotopy.refl
      (⟨Sum.inl, continuous_inl⟩ : C(C, C ⊕ D))).comp e.right_inv.some
    have G := (ContinuousMap.Homotopy.refl
      (⟨Sum.inr, continuous_inr⟩ : C(D, C ⊕ D))).comp f.right_inv.some
    have hh := (show ContinuousMap.Homotopic _ _ from ⟨sumDomainHomotopy F G⟩)
    convert hh using 1 <;> ext x <;> cases x <;> rfl

private abbrev OpenRect := Set.Ioo (0 : ℝ) 1 × Set.Ioo (-1 : ℝ) 1
private abbrev CutRect := {p : OpenRect // (p.2 : ℝ) ≠ 0}
private abbrev NegativeRect := Set.Ioo (0 : ℝ) 1 × Set.Ioo (-1 : ℝ) 0
private abbrev PositiveRect := Set.Ioo (0 : ℝ) 1 × Set.Ioo (0 : ℝ) 1
private def negativeSide : Set CutRect := {p | (p.val.2 : ℝ) < 0}

private theorem negativeSide_clopen : IsClopen negativeSide := by
  have heq : negativeSideᶜ = {p : CutRect | 0 < (p.val.2 : ℝ)} := by
    ext p
    change (¬ (p.val.2 : ℝ) < 0) ↔ 0 < (p.val.2 : ℝ)
    exact ⟨fun h => lt_of_le_of_ne (le_of_not_gt h) p.property.symm, fun h => not_lt.mpr h.le⟩
  refine ⟨isOpen_compl_iff.mp ?_, ?_⟩
  · rw [heq]
    exact isOpen_lt continuous_const (by fun_prop)
  · exact isOpen_lt (by fun_prop) continuous_const

private def cutRectSplit : (↥negativeSide ⊕ ↥negativeSideᶜ) ≃ₜ CutRect := by
  classical
  exact (Equiv.Set.sumCompl negativeSide).toHomeomorphOfContinuousOpen
    (continuous_subtype_val.sumElim continuous_subtype_val)
    (isOpenMap_sum.mpr ⟨negativeSide_clopen.isOpen.isOpenEmbedding_subtypeVal.isOpenMap,
      negativeSide_clopen.compl.isOpen.isOpenEmbedding_subtypeVal.isOpenMap⟩)

private def negativeSideChart : ↥negativeSide ≃ₜ NegativeRect where
  toFun p := (p.val.val.1, ⟨p.val.val.2, p.val.val.2.property.1, p.property⟩)
  invFun p := ⟨⟨(p.1, ⟨p.2, p.2.property.1, by linarith [p.2.property.2]⟩),
    ne_of_lt p.2.property.2⟩, p.2.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private def positiveSideChart : ↥negativeSideᶜ ≃ₜ PositiveRect where
  toFun p := (p.val.val.1, ⟨p.val.val.2,
    lt_of_le_of_ne (le_of_not_gt p.property) p.val.property.symm, p.val.val.2.property.2⟩)
  invFun p := ⟨⟨(p.1, ⟨p.2, by linarith [p.2.property.1], p.2.property.2⟩),
    ne_of_gt p.2.property.1⟩, not_lt.mpr p.2.property.1.le⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- An open rectangle cut along its full middle axis has exactly two
contractible components, with a genuine homotopy equivalence to two points. -/
def cutRectangleHomotopyTwo : CutRect ≃ₕ (Unit ⊕ Unit) := by
  letI : ContractibleSpace (Set.Ioo (0 : ℝ) 1) :=
    (convex_Ioo _ _).contractibleSpace ⟨1/2, by norm_num⟩
  letI : ContractibleSpace (Set.Ioo (-1 : ℝ) 0) :=
    (convex_Ioo _ _).contractibleSpace ⟨-1/2, by norm_num⟩
  let hn : ↥negativeSide ≃ₕ Unit := negativeSideChart.toHomotopyEquiv.trans
    (ContractibleSpace.hequiv_unit NegativeRect).some
  let hp : ↥negativeSideᶜ ≃ₕ Unit := positiveSideChart.toHomotopyEquiv.trans
    (ContractibleSpace.hequiv_unit PositiveRect).some
  exact cutRectSplit.symm.toHomotopyEquiv.trans (sumHomotopyEquiv hn hp)

end CurveComplexGenusTwo.SourceTopology.ThreeArcCut
