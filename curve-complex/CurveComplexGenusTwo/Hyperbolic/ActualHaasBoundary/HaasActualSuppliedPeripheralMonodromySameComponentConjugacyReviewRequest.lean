import Mathlib
open Set Topology
set_option maxHeartbeats 4000000
theorem actual_supplied_peripheral_monodromy_same_component_conjugacy {C U K : Type} [TopologicalSpace C] [TopologicalSpace U] [Group K]
    (a : MulAction K C) (q : C → U) (hq : letI := a;IsQuotientCoveringMap q K)
    (u v : U) (o : q ⁻¹' {u}) (y : q ⁻¹' {v})
    (stem : Path.Homotopic.Quotient u v) (γ : Path.Homotopic.Quotient v v)
    (δ η : K)
    (hδ : @SMul.smul K C a.toSMul δ o.val=
      (hq.isCoveringMap.monodromy (stem.trans (γ.symm.trans stem.symm)) o).val)
    (hη : @SMul.smul K C a.toSMul η y.val=
      (hq.isCoveringMap.monodromy γ y).val) :
    ∃k : K,δ=k⁻¹*η⁻¹*k := by
  letI := a
  let M {s t : U} := hq.isCoveringMap.monodromy (x:=s) (y:=t)
  let y₀ := M stem o
  obtain ⟨k,hk⟩ := hq.exists_toPermFiber_eq y₀ y
  refine ⟨k,?_⟩
  have hd : hq.toPermFiber u δ o=M (stem.trans (γ.symm.trans stem.symm)) o :=
    Subtype.ext hδ
  have he : hq.toPermFiber v η y=M γ y := Subtype.ext hη
  have htransport : hq.toPermFiber v δ y₀=M γ.symm y₀ := by
    have hh := congrArg (M stem) hd
    dsimp only [M] at hh ⊢
    rw [hq.monodromy_toPermFiber] at hh
    simp only [←hq.isCoveringMap.monodromy_trans_apply,
      Path.Homotopic.Quotient.trans_assoc,Path.Homotopic.Quotient.symm_trans,
      Path.Homotopic.Quotient.trans_refl] at hh
    rw [hq.isCoveringMap.monodromy_trans_apply] at hh
    exact hh
  have hcancel : M γ.symm (M γ y₀)=y₀ := by
    dsimp only [M]
    rw [←hq.isCoveringMap.monodromy_trans_apply,Path.Homotopic.Quotient.trans_symm,
      hq.isCoveringMap.monodromy_refl]
    rfl
  have hm : hq.toPermFiber v η (hq.toPermFiber v k y₀)=
      hq.toPermFiber v k (M γ y₀) := by
    rw [hk,he,←hq.monodromy_toPermFiber,hk]
  have hm' : hq.toPermFiber v (k⁻¹*η*k) y₀=M γ y₀ := by
    apply (hq.toPermFiber v k).injective
    simpa using hm
  have hunit : hq.toPermFiber v ((k⁻¹*η*k)*δ) y₀=y₀ := by
    rw [map_mul,Equiv.Perm.mul_apply,htransport]
    rw [←hq.monodromy_toPermFiber,hm']
    exact hcancel
  have heq : (k⁻¹*η*k)*δ=1 := hq.toPermFiber_ext v y₀ (by simpa using hunit)
  calc
    δ=(k⁻¹*η*k)⁻¹ := by exact eq_inv_of_mul_eq_one_right heq
    _=k⁻¹*η⁻¹*k := by group

