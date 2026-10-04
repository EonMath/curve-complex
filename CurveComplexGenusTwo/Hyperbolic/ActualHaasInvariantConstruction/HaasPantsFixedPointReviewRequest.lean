import Mathlib
open Topology
namespace CurveComplex.Hyperbolic

theorem pants_swapped_generators_twisted_cocycle (g : FreeGroup Bool) (hc : g * FreeGroup.map Bool.not g = 1) :
    ∃ h : FreeGroup Bool, g = h * (FreeGroup.map Bool.not h)⁻¹ := by
  have hhalf {α : Type} (τ : α → α) (hinv : Function.Involutive τ)
      (hfree : ∀ a, τ a ≠ a) (w : List α)
      (hsym : w = (w.map τ).reverse) :
      ∃ u : List α, w = u ++ (u.map τ).reverse := by
    induction w using List.bidirectionalRecOn with
    | H0 => exact ⟨[],rfl⟩
    | H1 a =>
      have he : a = τ a := by simpa using hsym
      exact (hfree a he.symm).elim
    | Hn a w b ih =>
      simp only [List.map_cons,List.map_append,List.map_singleton,
        List.reverse_cons,List.reverse_append,List.reverse_singleton] at hsym
      have hab : a = τ b := List.head_eq_of_cons_eq hsym
      have htail := List.tail_eq_of_cons_eq hsym
      have hm : w = (w.map τ).reverse := List.append_inj_left' htail (by simp)
      obtain ⟨u,hu⟩ := ih hm
      have hba : b = τ a := by rw [hab,hinv]
      refine ⟨a::u,?_⟩
      simp only [List.map_cons,List.reverse_cons,List.cons_append]
      simp only [hu,hba,List.append_assoc]
  have hmap (k : FreeGroup Bool) :
      (FreeGroup.map Bool.not k).toWord = k.toWord.map (fun x => (!x.1,x.2)) := by
    have hred : FreeGroup.IsReduced (k.toWord.map (fun x => (!x.1,x.2))) := by
      apply List.isChain_map_of_isChain (fun x : Bool × Bool => (!x.1,x.2))
        (fun a b hab hh => hab (by simpa using congrArg Bool.not hh))
        FreeGroup.isReduced_toWord
    rw [←FreeGroup.mk_toWord (x := k),FreeGroup.map.mk,FreeGroup.toWord_mk,hred.reduce_eq]
    rw [FreeGroup.mk_toWord]
  have he : g = (FreeGroup.map Bool.not g)⁻¹ := eq_inv_iff_mul_eq_one.mpr hc
  have ht := congrArg FreeGroup.toWord he
  rw [FreeGroup.toWord_inv,hmap] at ht
  let τ : Bool × Bool → Bool × Bool := fun x => (!x.1,!x.2)
  have hτ : Function.Involutive τ := by intro x;rcases x with ⟨a,b⟩;simp [τ]
  have hf : ∀ x, τ x ≠ x := by
    intro x he
    have hb := congrArg Prod.snd he
    cases x.2 <;> simp [τ] at hb
  have htw : g.toWord = (g.toWord.map τ).reverse := by
    simpa [FreeGroup.invRev,List.map_map,Function.comp_def,τ] using ht
  obtain ⟨u,hu⟩ := hhalf τ hτ hf g.toWord htw
  refine ⟨FreeGroup.mk u,?_⟩
  calc
    g = FreeGroup.mk g.toWord := FreeGroup.mk_toWord.symm
    _ = FreeGroup.mk u * (FreeGroup.map Bool.not (FreeGroup.mk u))⁻¹ := by
      rw [FreeGroup.map.mk,FreeGroup.inv_mk,FreeGroup.mul_mk]
      congr 1
      simpa [FreeGroup.invRev,List.map_map,Function.comp_def,τ] using hu

theorem pants_actual_free_quotient_has_one_fixed_point {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [MulAction (FreeGroup Bool) X]
    (q : X → Y) (hqs : Function.Surjective q)
    (hfib : ∀ x z, q x = q z ↔ ∃ g : FreeGroup Bool, g • x = z)
    (hfree : ∀ (g : FreeGroup Bool) (x : X), g • x = x → g = 1)
    (j : X ≃ₜ X) (hjinv : Function.Involutive j)
    (hjtw : ∀ (g : FreeGroup Bool) (x : X),
      j (g • x) = FreeGroup.map Bool.not g • j x)
    (c : X) (hcenter : ∀ x, j x = x ↔ x = c)
    (J : Y ≃ₜ Y) (hdesc : ∀ x, J (q x) = q (j x)) :
    ∀ y, J y = y ↔ y = q c := by
  have hcocycle (g : FreeGroup Bool) (hc : g * FreeGroup.map Bool.not g = 1) :
      ∃ h : FreeGroup Bool, g = h * (FreeGroup.map Bool.not h)⁻¹ := by
    have hhalf {α : Type} (τ : α → α) (hinv : Function.Involutive τ)
        (hfree : ∀ a, τ a ≠ a) (w : List α)
        (hsym : w = (w.map τ).reverse) :
        ∃ u : List α, w = u ++ (u.map τ).reverse := by
      induction w using List.bidirectionalRecOn with
      | H0 => exact ⟨[],rfl⟩
      | H1 a =>
        have he : a = τ a := by simpa using hsym
        exact (hfree a he.symm).elim
      | Hn a w b ih =>
        simp only [List.map_cons,List.map_append,List.map_singleton,
          List.reverse_cons,List.reverse_append,List.reverse_singleton] at hsym
        have hab : a = τ b := List.head_eq_of_cons_eq hsym
        have htail := List.tail_eq_of_cons_eq hsym
        have hm : w = (w.map τ).reverse := List.append_inj_left' htail (by simp)
        obtain ⟨u,hu⟩ := ih hm
        have hba : b = τ a := by rw [hab,hinv]
        refine ⟨a::u,?_⟩
        simp only [List.map_cons,List.reverse_cons,List.cons_append]
        simp only [hu,hba,List.append_assoc]
    have hmap (k : FreeGroup Bool) :
        (FreeGroup.map Bool.not k).toWord = k.toWord.map (fun x => (!x.1,x.2)) := by
      have hred : FreeGroup.IsReduced (k.toWord.map (fun x => (!x.1,x.2))) := by
        apply List.isChain_map_of_isChain (fun x : Bool × Bool => (!x.1,x.2))
          (fun a b hab hh => hab (by simpa using congrArg Bool.not hh))
          FreeGroup.isReduced_toWord
      rw [←FreeGroup.mk_toWord (x := k),FreeGroup.map.mk,FreeGroup.toWord_mk,hred.reduce_eq]
      rw [FreeGroup.mk_toWord]
    have he : g = (FreeGroup.map Bool.not g)⁻¹ := eq_inv_iff_mul_eq_one.mpr hc
    have ht := congrArg FreeGroup.toWord he
    rw [FreeGroup.toWord_inv,hmap] at ht
    let τ : Bool × Bool → Bool × Bool := fun x => (!x.1,!x.2)
    have hτ : Function.Involutive τ := by intro x;rcases x with ⟨a,b⟩;simp [τ]
    have hf : ∀ x, τ x ≠ x := by
      intro x he
      have hb := congrArg Prod.snd he
      cases x.2 <;> simp [τ] at hb
    have htw : g.toWord = (g.toWord.map τ).reverse := by
      simpa [FreeGroup.invRev,List.map_map,Function.comp_def,τ] using ht
    obtain ⟨u,hu⟩ := hhalf τ hτ hf g.toWord htw
    refine ⟨FreeGroup.mk u,?_⟩
    calc
      g = FreeGroup.mk g.toWord := FreeGroup.mk_toWord.symm
      _ = FreeGroup.mk u * (FreeGroup.map Bool.not (FreeGroup.mk u))⁻¹ := by
        rw [FreeGroup.map.mk,FreeGroup.inv_mk,FreeGroup.mul_mk]
        congr 1
        simpa [FreeGroup.invRev,List.map_map,Function.comp_def,τ] using hu
  let σ : FreeGroup Bool →* FreeGroup Bool := FreeGroup.map Bool.not
  have hσ (g : FreeGroup Bool) : σ (σ g) = g := by
    simp [σ,FreeGroup.map.comp,Function.comp_def]
  intro y
  obtain ⟨x,rfl⟩ := hqs y
  constructor
  · intro hy
    have he : q x = q (j x) := by rw [←hdesc,hy]
    obtain ⟨g,hg⟩ := (hfib x (j x)).mp he
    have hgf : σ g * g = 1 := by
      apply hfree _ x
      rw [mul_smul,hg]
      change FreeGroup.map Bool.not g • j x = x
      rw [←hjtw,hg,hjinv]
    have hginv : σ g = g⁻¹ := eq_inv_iff_mul_eq_one.mpr hgf
    have hgc : g * σ g = 1 := by rw [hginv];simp
    obtain ⟨h,hh⟩ := hcocycle g hgc
    let k := σ h
    have hgk : g = σ k * k⁻¹ := by
      simpa only [k,hσ,σ] using hh
    have hprod : σ (k⁻¹) * g = k⁻¹ := by rw [map_inv,hgk];group
    have hkfix : j (k⁻¹ • x) = k⁻¹ • x := by
      calc
        j (k⁻¹ • x) = σ (k⁻¹) • j x := hjtw _ _
        _ = σ (k⁻¹) • (g • x) := by rw [hg]
        _ = (σ (k⁻¹) * g) • x := (mul_smul _ _ _).symm
        _ = k⁻¹ • x := by rw [hprod]
    exact (hfib x c).mpr ⟨k⁻¹,(hcenter _).mp hkfix⟩
  · intro hy
    rw [hy,hdesc,(hcenter c).mpr rfl]

theorem actual_twisted_torus_seam_has_two_fixed_points (u : Circle) :
    Function.Involutive (fun z : Circle => u * z⁻¹) ∧
    ∃ F : Finset Circle, F.card = 2 ∧ (F : Set Circle) = {z | u * z⁻¹ = z} := by
  classical
  constructor
  · intro z
    simp [mul_comm]
  · obtain ⟨θ,rfl⟩ := Circle.exp_surjective u
    let a : Circle := Circle.exp (θ/2)
    have ha : a^2 = Circle.exp θ := by
      dsimp [a]
      rw [pow_two,←Circle.exp_add]
      congr 1
      ring
    have hiff (z : Circle) : Circle.exp θ * z⁻¹ = z ↔ z = a ∨ z = -a := by
      constructor
      · intro h
        have ht := congrArg (fun w : Circle => w*z) h
        simp only [mul_assoc,inv_mul_cancel,mul_one] at ht
        have hs : (z : ℂ)^2 = (a : ℂ)^2 := by
          have hh : z^2 = a^2 := by rw [pow_two,←ht,ha]
          simpa only [Circle.coe_pow] using congrArg (fun z : Circle => (z : ℂ)) hh
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with he | he
        · exact Or.inl (Circle.coe_injective he)
        · exact Or.inr (Circle.coe_injective (by simpa using he))
      · rintro (rfl | rfl)
        · rw [←ha,pow_two]
          group
        · apply Circle.coe_injective
          rw [←ha]
          simp only [Circle.coe_mul,Circle.coe_inv,Circle.coe_pow,Circle.coe_neg]
          field_simp [Circle.coe_ne_zero a]
          <;> ring
    refine ⟨{a,-a},?_,?_⟩
    · simp [Circle.neg_ne_self a,(Circle.neg_ne_self a).symm]
    · ext z
      simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton,Set.mem_setOf_eq]
      exact (hiff z).symm

end CurveComplex.Hyperbolic
