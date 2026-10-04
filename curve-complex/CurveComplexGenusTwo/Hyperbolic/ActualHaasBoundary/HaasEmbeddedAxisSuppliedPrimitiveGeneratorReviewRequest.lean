import Mathlib
open Set
theorem actual_embedded_axis_supplied_translation_is_primitive {G P E : Type} [Group G] (a : MulAction G P)
    (p : P → E) (α : ℝ → P) (hα : Function.Injective α) (T : ℝ) (hT : 0 < T)
    (hp : ∀ g : G, ∀ x : P, p (@SMul.smul G P a.toSMul g x)=p x)
    (hfibre : ∀ s t : ℝ, p (α s)=p (α t) ↔ ∃ n : ℤ,s=t+n*T)
    (σ : Additive G →+ ℝ) (hσ : Function.Injective σ)
    (htranslate : ∀ g : G,∀ t : ℝ,
      @SMul.smul G P a.toSMul g (α t)=α (t+σ (Additive.ofMul g)))
    (δ : G) (hδ : ∀ t : ℝ, @SMul.smul G P a.toSMul δ (α t)=α (t+T)) :
    (∀ g : G,∃ n : ℤ,g=δ^n) ∧ σ.range=AddSubgroup.zmultiples T := by
  have hδvalue : σ (Additive.ofMul δ)=T := by
    have h := (htranslate δ 0).symm.trans (hδ 0)
    simpa using hα h
  have hvalue (g : G) : ∃ n : ℤ,σ (Additive.ofMul g)=(n:ℝ)*T := by
    have h := hp g (α 0)
    rw [htranslate,zero_add] at h
    obtain ⟨n,hn⟩ := (hfibre _ _).mp h
    exact ⟨n,by simpa using hn⟩
  have hpow (n : ℤ) : σ (Additive.ofMul (δ^n))=(n:ℝ)*T := by
    change σ (n • Additive.ofMul δ)=(n:ℝ)*T
    rw [map_zsmul,hδvalue,zsmul_eq_mul]
  constructor
  · intro g
    obtain ⟨n,hn⟩ := hvalue g
    have he : Additive.ofMul g=Additive.ofMul (δ^n) := hσ (hn.trans (hpow n).symm)
    exact ⟨n,congrArg Additive.toMul he⟩
  · ext r
    constructor
    · rintro ⟨g,hg⟩
      obtain ⟨n,hn⟩ := hvalue g.toMul
      apply AddSubgroup.mem_zmultiples_iff.mpr
      exact ⟨n,by simpa [zsmul_eq_mul] using hn.symm.trans hg⟩
    · intro hr
      obtain ⟨n,hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hr
      exact ⟨Additive.ofMul (δ^n),(hpow n).trans (by simpa [zsmul_eq_mul] using hn)⟩
