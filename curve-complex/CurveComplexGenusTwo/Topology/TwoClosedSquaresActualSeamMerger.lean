import Mathlib

open Set Topology

-- A genuine disk-merger model: two closed squares attached along exactly
-- their facing vertical sides form one closed square, with the actual
-- affine maps on both pieces and the exact seam fibers proved.
theorem two_closed_squares_actual_seam_merger :
    let D := unitInterval × unitInterval
    ∃ f : C(D ⊕ D, D), Function.Surjective f ∧
      Function.Injective (fun x => f (Sum.inl x)) ∧
      Function.Injective (fun x => f (Sum.inr x)) ∧
      (∀ x y : D, f (Sum.inl x) = f (Sum.inr y) ↔
        x.1 = 1 ∧ y.1 = 0 ∧ x.2 = y.2) ∧
      Nonempty (Quotient (Setoid.ker f) ≃ₜ D) := by
  classical
  let D := unitInterval × unitInterval
  let L : D → D := fun x =>
    (⟨x.1.val / 2, ⟨by linarith [x.1.property.1], by linarith [x.1.property.2]⟩⟩, x.2)
  let R : D → D := fun x =>
    (⟨(x.1.val + 1) / 2, ⟨by linarith [x.1.property.1], by linarith [x.1.property.2]⟩⟩, x.2)
  have hL : Continuous L := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact (continuous_subtype_val.comp continuous_fst).div_const 2
    · exact continuous_snd
  have hR : Continuous R := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact ((continuous_subtype_val.comp continuous_fst).add_const 1).div_const 2
    · exact continuous_snd
  let f : C(D ⊕ D,D) := ⟨Sum.elim L R, hL.sumElim hR⟩
  have hs : Function.Surjective f := by
    intro x
    by_cases hx : x.1.val ≤ 1/2
    · refine ⟨Sum.inl (⟨2*x.1.val, ⟨by linarith [x.1.property.1], by linarith⟩⟩,x.2), ?_⟩
      apply Prod.ext
      · apply Subtype.ext
        dsimp [f,L]
        ring
      · rfl
    · refine ⟨Sum.inr (⟨2*x.1.val-1, ⟨by linarith, by linarith [x.1.property.2]⟩⟩,x.2), ?_⟩
      apply Prod.ext
      · apply Subtype.ext
        dsimp [f,R]
        ring
      · rfl
  have hiL : Function.Injective (fun x => f (Sum.inl x)) := by
    intro x y h
    apply Prod.ext
    · apply Subtype.ext
      have h₁ := congrArg (fun z : D => z.1.val) h
      dsimp [f,L] at h₁
      linarith
    · simpa [f,L,R] using congrArg (fun z : D => z.2) h
  have hiR : Function.Injective (fun x => f (Sum.inr x)) := by
    intro x y h
    apply Prod.ext
    · apply Subtype.ext
      have h₁ := congrArg (fun z : D => z.1.val) h
      dsimp [f,R] at h₁
      linarith
    · simpa [f,L,R] using congrArg (fun z : D => z.2) h
  have hseam (x y : D) : f (Sum.inl x) = f (Sum.inr y) ↔
      x.1 = 1 ∧ y.1 = 0 ∧ x.2 = y.2 := by
    constructor
    · intro h
      have h₁ := congrArg (fun z : D => z.1.val) h
      dsimp [f,L,R] at h₁
      refine ⟨Subtype.ext ?_, Subtype.ext ?_, by simpa [f,L,R] using congrArg (fun z : D => z.2) h⟩
      · change x.1.val = 1
        linarith [x.1.property.2,y.1.property.1]
      · change y.1.val = 0
        linarith [x.1.property.2,y.1.property.1]
    · rintro ⟨hx,hy,h₂⟩
      apply Prod.ext
      · apply Subtype.ext
        dsimp [f,L,R]
        rw [hx,hy]
        norm_num
      · exact h₂
  let q : Quotient (Setoid.ker f) → D := Quotient.lift f (fun x y h => h)
  have hq : Continuous q := f.continuous.quotient_lift _
  have hiq : Function.Injective q := by
    intro x y h
    induction x using Quotient.inductionOn with
    | _ x =>
      induction y using Quotient.inductionOn with
      | _ y => exact Quotient.sound h
  have hsq : Function.Surjective q := by
    intro y
    obtain ⟨x,hx⟩ := hs y
    exact ⟨Quotient.mk (Setoid.ker f) x,hx⟩
  let e := Equiv.ofBijective q ⟨hiq,hsq⟩
  exact ⟨f,hs,hiL,hiR,hseam,⟨(show Continuous (e : Quotient (Setoid.ker f) → D) from hq).homeoOfEquivCompactToT2⟩⟩
