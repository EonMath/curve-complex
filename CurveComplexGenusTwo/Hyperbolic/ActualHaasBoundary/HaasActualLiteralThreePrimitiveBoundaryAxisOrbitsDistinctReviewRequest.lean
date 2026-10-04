import Mathlib
open Set
open scoped Pointwise
set_option maxHeartbeats 3000000
theorem actual_literal_three_primitive_boundary_axis_orbits_distinct {K G P : Type} [Group K] [Group G]
    (a : MulAction G P) (B : FreeGroup (Fin 2) ≃* Kᵐᵒᵖ)
    (ι : K →* G) (hι : Function.Injective ι) (S₀ S₁ Sc : Set P) (σ : ℤ)
    (hprim₁ : ∀g : G,(fun z => @SMul.smul G P a.toSMul g z) '' S₁=S₁ →
      ∃n : ℤ,g=(ι (B (FreeGroup.of 1)).unop)^n)
    (hprimc : ∀g : G,(fun z => @SMul.smul G P a.toSMul g z) '' Sc=Sc →
      ∃n : ℤ,g=(ι (B ((FreeGroup.of 0*(FreeGroup.of 1)⁻¹)^σ)).unop)^n)
    (hpres₀ : (fun z => @SMul.smul G P a.toSMul (ι (B (FreeGroup.of 0)).unop) z) '' S₀=S₀)
    (hpres₁ : (fun z => @SMul.smul G P a.toSMul (ι (B (FreeGroup.of 1)).unop) z) '' S₁=S₁) :
    (∀k : K,(fun z => @SMul.smul G P a.toSMul (ι k) z) '' S₀≠S₁) ∧
    (∀k : K,(fun z => @SMul.smul G P a.toSMul (ι k) z) '' S₀≠Sc) ∧
    (∀k : K,(fun z => @SMul.smul G P a.toSMul (ι k) z) '' S₁≠Sc) := by
  have hDistinct {K G P : Type} [Group K] [Group G]
      (a : MulAction G P) (B : FreeGroup (Fin 2) ≃* Kᵐᵒᵖ)
      (ι : K →* G) (hι : Function.Injective ι) (S₀ S₁ : Set P)
      (u v : FreeGroup (Fin 2)) (χ : FreeGroup (Fin 2) →* Multiplicative ℤ)
      (hχu : χ u≠1) (hχv : χ v=1)
      (hprim : ∀g : G,(fun z => @SMul.smul G P a.toSMul g z) '' S₁=S₁ →
        ∃n : ℤ,g=(ι (B v).unop)^n)
      (hpres : (fun z => @SMul.smul G P a.toSMul (ι (B u).unop) z) '' S₀=S₀) :
      ∀k : K,(fun z => @SMul.smul G P a.toSMul (ι k) z) '' S₀≠S₁ := by
    letI := a
    intro k horbit
    have horbit' : ι k • S₀=S₁ := horbit
    have hpres' : ι (B u).unop • S₀=S₀ := hpres
    have hconj : (ι k*(ι (B u).unop)*(ι k)⁻¹) • S₁=S₁ := by
      rw [←horbit',mul_smul,mul_smul,inv_smul_smul,hpres']
    obtain ⟨n,hn⟩ := hprim (ι k*(ι (B u).unop)*(ι k)⁻¹) hconj
    have hk : k*(B u).unop*k⁻¹=((B v).unop)^n := by
      apply hι
      simpa only [map_mul,map_inv,map_zpow] using hn
    let w := B.symm (MulOpposite.op k)
    have hword : w⁻¹*u*w=v^n := by
      apply B.injective
      apply MulOpposite.unop_injective
      simpa [w,map_mul,map_inv,map_zpow,MulOpposite.unop_mul,mul_assoc] using hk
    have hc := congrArg χ hword
    apply hχu
    simpa [map_mul,map_inv,map_zpow,hχv,mul_comm,mul_left_comm,mul_assoc] using hc
  let χ₀ : FreeGroup (Fin 2) →* Multiplicative ℤ :=
    FreeGroup.lift (fun i => if i=0 then Multiplicative.ofAdd 1 else 1)
  let χsum : FreeGroup (Fin 2) →* Multiplicative ℤ :=
    FreeGroup.lift (fun _ => Multiplicative.ofAdd 1)
  have hχ₀ : χ₀ (FreeGroup.of 0)≠1 := by
    simp [χ₀]
  have hχ₁ : χ₀ (FreeGroup.of 1)=1 := by simp [χ₀]
  have hχs₀ : χsum (FreeGroup.of 0)≠1 := by simp [χsum]
  have hχs₁ : χsum (FreeGroup.of 1)≠1 := by simp [χsum]
  have hχsc : χsum ((FreeGroup.of 0*(FreeGroup.of 1)⁻¹)^σ)=1 := by simp [χsum]
  exact ⟨hDistinct a B ι hι S₀ S₁ (FreeGroup.of 0) (FreeGroup.of 1) χ₀ hχ₀ hχ₁ hprim₁ hpres₀,
    hDistinct a B ι hι S₀ Sc (FreeGroup.of 0) ((FreeGroup.of 0*(FreeGroup.of 1)⁻¹)^σ)
      χsum hχs₀ hχsc hprimc hpres₀,
    hDistinct a B ι hι S₁ Sc (FreeGroup.of 1) ((FreeGroup.of 0*(FreeGroup.of 1)⁻¹)^σ)
      χsum hχs₁ hχsc hprimc hpres₁⟩
