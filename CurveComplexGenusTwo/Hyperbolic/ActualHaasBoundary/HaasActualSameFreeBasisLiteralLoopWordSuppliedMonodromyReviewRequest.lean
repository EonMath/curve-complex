import Mathlib
open Set Topology
set_option maxHeartbeats 3000000
theorem actual_same_free_basis_literal_loop_word_supplied_monodromy {U C K : Type} [TopologicalSpace U] [TopologicalSpace C]
    [SimplyConnectedSpace C] [Group K] (a : MulAction K C) (q : C → U)
    (hq : letI := a;IsQuotientCoveringMap q K) (u : U) (o : q ⁻¹' {u})
    (B : FreeGroup (Fin 2) ≃* Kᵐᵒᵖ) (γ₀ γ₁ : Path.Homotopic.Quotient u u)
    (h₀ : @SMul.smul K C a.toSMul (B (FreeGroup.of 0)).unop o.val=
      (hq.isCoveringMap.monodromy γ₀ o).val)
    (h₁ : @SMul.smul K C a.toSMul (B (FreeGroup.of 1)).unop o.val=
      (hq.isCoveringMap.monodromy γ₁ o).val) :
    @SMul.smul K C a.toSMul (B ((FreeGroup.of 1)⁻¹*FreeGroup.of 0)).unop o.val=
      (hq.isCoveringMap.monodromy (γ₀.trans γ₁.symm) o).val := by
  letI := a
  let κ := hq.fundamentalGroupEquiv o
  have hmono (γ : FundamentalGroup U u) :
      @SMul.smul K C a.toSMul (κ γ).unop o.val=
        (hq.isCoveringMap.monodromy γ.toPath o).val :=
    hq.unop_fundamentalGroupToMulOpposite_smul (e:=o) (γ:=γ)
  have hk₀ : κ (FundamentalGroup.fromPath γ₀)=B (FreeGroup.of 0) := by
    apply MulOpposite.unop_injective
    letI := hq.isCancelSMul
    apply IsCancelSMul.right_cancel' _ _ o.val
    exact (hmono (FundamentalGroup.fromPath γ₀)).trans h₀.symm
  have hk₁ : κ (FundamentalGroup.fromPath γ₁)=B (FreeGroup.of 1) := by
    apply MulOpposite.unop_injective
    letI := hq.isCancelSMul
    apply IsCancelSMul.right_cancel' _ _ o.val
    exact (hmono (FundamentalGroup.fromPath γ₁)).trans h₁.symm
  have hword : κ (FundamentalGroup.fromPath (γ₀.trans γ₁.symm))=
      B ((FreeGroup.of 1)⁻¹*FreeGroup.of 0) := by
    change κ ((FundamentalGroup.fromPath γ₁)⁻¹*FundamentalGroup.fromPath γ₀)=_
    rw [map_mul,map_inv,hk₁,hk₀,←map_inv,←map_mul]
  have hm := hmono (FundamentalGroup.fromPath (γ₀.trans γ₁.symm))
  rw [hword] at hm
  exact hm

