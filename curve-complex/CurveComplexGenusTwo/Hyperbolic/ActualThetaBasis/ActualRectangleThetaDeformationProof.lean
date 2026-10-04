import CurveComplexGenusTwo.Hyperbolic.ActualThetaBasis.ActualSquareThetaCover
open Set Topology ContinuousMap
namespace CurveComplex.Hyperbolic.PantsTheta
theorem actual_rectangle_theta_deformation :
    let P := {z : ℝ × ℝ // z ≠ ((-1/2 : ℝ),0) ∧ z ≠ ((1/2 : ℝ),0)}
    let B := {z : P // ‖z.val‖ ≤ 1}
    ∃ r : B ≃ₕ ActualSquareTheta, ∀ z,
      (r z).val =
        let c : ℝ := if z.val.val.1 ≤ 0 then -1/2 else 1/2
        let w : ℝ × ℝ := (2*(z.val.val.1-c),z.val.val.2)
        (c+(‖w‖)⁻¹*w.1/2,(‖w‖)⁻¹*w.2) := by
  classical
  intro P B
  have hsquare (w : ℝ × ℝ) (hw : ‖w‖=1) :
      (-1 ≤ w.1 ∧ w.1 ≤ 1) ∧ (-1 ≤ w.2 ∧ w.2 ≤ 1) ∧
      (w.1=-1 ∨ w.1=1 ∨ w.2=-1 ∨ w.2=1) := by
    have hx : |w.1| ≤ 1 := (norm_fst_le w).trans hw.le
    have hy : |w.2| ≤ 1 := (norm_snd_le w).trans hw.le
    refine ⟨abs_le.mp hx,abs_le.mp hy,?_⟩
    have hmax : max |w.1| |w.2|=1 := by simpa [Prod.norm_def,Real.norm_eq_abs] using hw
    have ha : |w.1|=1 ∨ |w.2|=1 := by
      by_cases h : |w.1| ≤ |w.2|
      · exact Or.inr (by simpa [max_eq_right h] using hmax)
      · exact Or.inl (by simpa [max_eq_left (le_of_not_ge h)] using hmax)
    rcases ha with hx|hy
    · by_cases h : 0 ≤ w.1
      · exact Or.inr (Or.inl (by simpa [abs_of_nonneg h] using hx))
      · exact Or.inl (by rw [abs_of_neg (lt_of_not_ge h)] at hx;linarith)
    · by_cases h : 0 ≤ w.2
      · exact Or.inr (Or.inr (Or.inr (by simpa [abs_of_nonneg h] using hy)))
      · exact Or.inr (Or.inr (Or.inl (by rw [abs_of_neg (lt_of_not_ge h)] at hy;linarith)))
  let c (side : Bool) : ℝ := if side then 1/2 else -1/2
  let g (side : Bool) (z : B) : ℝ × ℝ := (2*(z.val.val.1-c side),z.val.val.2)
  have hg0 (side : Bool) (z : B) : g side z ≠ 0 := by
    intro h
    have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    cases side
    · apply z.val.property.1
      apply Prod.ext
      · dsimp [g,c] at hx ⊢;linarith
      · exact hy
    · apply z.val.property.2
      apply Prod.ext
      · dsimp [g,c] at hx ⊢;linarith
      · exact hy
  let u (side : Bool) (z : B) : ℝ × ℝ := ‖g side z‖⁻¹ • g side z
  have hu (side : Bool) (z : B) : ‖u side z‖=1 := by
    simp [u,norm_smul,norm_ne_zero_iff.mpr (hg0 side z)]
  have hmem (side : Bool) (z : B) :
      ((c side+(u side z).1/2,(u side z).2) : ℝ × ℝ) ∈
        {z : ℝ × ℝ | ((-1 ≤ z.1 ∧ z.1 ≤ 1) ∧ (z.2=-1 ∨ z.2=1)) ∨
          ((z.1=-1 ∨ z.1=0 ∨ z.1=1) ∧ (-1 ≤ z.2 ∧ z.2 ≤ 1))} := by
    obtain ⟨hx,hy,hb⟩ := hsquare (u side z) (hu side z)
    rcases hb with h|h|h|h
    · right
      refine ⟨?_,hy⟩
      cases side <;> norm_num [c,h]
    · right
      refine ⟨?_,hy⟩
      cases side <;> norm_num [c,h]
    · left
      refine ⟨?_,Or.inl h⟩
      cases side <;> dsimp [c] <;> constructor <;> linarith [hx.1,hx.2]
    · left
      refine ⟨?_,Or.inr h⟩
      cases side <;> dsimp [c] <;> constructor <;> linarith [hx.1,hx.2]
  let f (side : Bool) : C(B,ActualSquareTheta) := {
    toFun z := ⟨(c side+(u side z).1/2,(u side z).2),hmem side z⟩
    continuous_toFun := by
      have hpoint : Continuous (fun z : B => z.val.val) := continuous_subtype_val.comp continuous_subtype_val
      have hg : Continuous (g side) :=
        (continuous_const.mul (hpoint.fst.sub continuous_const)).prodMk hpoint.snd
      have huC : Continuous (u side) :=
        ((continuous_norm.comp hg).inv₀ (fun z => norm_ne_zero_iff.mpr (hg0 side z))).smul hg
      apply Continuous.subtype_mk
      exact (continuous_const.add (huC.fst.div_const 2)).prodMk huC.snd }
  have hseam (z : B) (hz : z.val.val.1=0) : f false z=f true z := by
    have hy : |z.val.val.2| ≤ 1 := (norm_snd_le z.val.val).trans z.property
    have hL : ‖g false z‖=1 := by simp [g,c,hz,Prod.norm_def,Real.norm_eq_abs,max_eq_left hy]
    have hR : ‖g true z‖=1 := by simp [g,c,hz,Prod.norm_def,Real.norm_eq_abs,max_eq_left hy]
    apply Subtype.ext
    dsimp [f,u]
    rw [hL,hR]
    norm_num [g,c,hz]
  let r : C(B,ActualSquareTheta) := {
    toFun z := if z.val.val.1 ≤ 0 then f false z else f true z
    continuous_toFun := (f false).continuous.if (fun z hz => hseam z
      (frontier_le_subset_eq (show Continuous (fun x : B => x.val.val.1) from
        (continuous_subtype_val.comp continuous_subtype_val).fst) continuous_const hz)) (f true).continuous }
  have hrect (z : ActualSquareTheta) : ‖z.val‖ ≤ 1 := by
    apply norm_prod_le_iff.mpr
    rcases z.property with h|h
    · exact ⟨by simpa [Real.norm_eq_abs] using abs_le.mpr h.1,
        by rcases h.2 with h|h <;> simp [h]⟩
    · exact ⟨by rcases h.1 with h|h|h <;> simp [h],
        by simpa [Real.norm_eq_abs] using abs_le.mpr h.2⟩
  have havoid (z : ActualSquareTheta) :
      z.val ≠ ((-1/2 : ℝ),0) ∧ z.val ≠ ((1/2 : ℝ),0) := by
    constructor <;> intro h <;> have hm := z.property <;> rw [h] at hm <;> norm_num at hm
  let i : C(ActualSquareTheta,B) := {
    toFun z := ⟨⟨z.val,havoid z⟩,hrect z⟩
    continuous_toFun := continuous_subtype_val.subtype_mk _ |>.subtype_mk _ }
  have hDfix (z : ActualSquareTheta) (side : Bool)
      (hs : if side then 0 < z.val.1 else z.val.1 ≤ 0) : ‖g side (i z)‖=1 := by
    have hx : -1 ≤ z.val.1 ∧ z.val.1 ≤ 1 := abs_le.mp
      (by simpa [Real.norm_eq_abs] using (norm_fst_le z.val).trans (hrect z))
    have hy : -1 ≤ z.val.2 ∧ z.val.2 ≤ 1 := abs_le.mp
      (by simpa [Real.norm_eq_abs] using (norm_snd_le z.val).trans (hrect z))
    cases side
    · have hw : |2*(z.val.1-(-1/2 : ℝ))| ≤ 1 := abs_le.mpr ⟨by dsimp at hs;linarith,by dsimp at hs;linarith⟩
      have hv : |z.val.2| ≤ 1 := abs_le.mpr hy
      change max |2*(z.val.1-(-1/2 : ℝ))| |z.val.2|=1
      rcases z.property with h|h
      · rcases h.2 with h|h <;> simp only [h,abs_neg,abs_one] <;> exact max_eq_right hw
      · rcases h.1 with h|h|h
        · rw [h];norm_num [max_eq_left hv]
        · rw [h];norm_num [max_eq_left hv]
        · dsimp at hs;linarith
    · have hw : |2*(z.val.1-(1/2 : ℝ))| ≤ 1 := abs_le.mpr ⟨by dsimp at hs;linarith,by dsimp at hs;linarith⟩
      have hv : |z.val.2| ≤ 1 := abs_le.mpr hy
      change max |2*(z.val.1-(1/2 : ℝ))| |z.val.2|=1
      rcases z.property with h|h
      · rcases h.2 with h|h <;> simp only [h,abs_neg,abs_one] <;> exact max_eq_right hw
      · rcases h.1 with h|h|h
        · dsimp at hs;linarith
        · dsimp at hs;linarith
        · rw [h];norm_num [max_eq_left hv]
  have hfix (z : ActualSquareTheta) : r (i z)=z := by
    apply Subtype.ext
    change (if z.val.1 ≤ 0 then f false (i z) else f true (i z)).val=z.val
    by_cases hz : z.val.1 ≤ 0
    · rw [ite_eq_left hz]
      have hd := hDfix z false hz
      dsimp [f,u]
      rw [hd]
      apply Prod.ext <;> dsimp [g,c,i] <;> ring
    · rw [ite_eq_right hz]
      have hd := hDfix z true (lt_of_not_ge hz)
      dsimp [f,u]
      rw [hd]
      apply Prod.ext <;> dsimp [g,c,i] <;> ring
  have hrside (z : B) :
      if z.val.val.1 ≤ 0 then (r z).val.1 ≤ 0 else 0 ≤ (r z).val.1 := by
    dsimp [r]
    split_ifs with hz
    · have hx := (hsquare (u false z) (hu false z)).1.2
      dsimp [f,c];linarith
    · have hx := (hsquare (u true z) (hu true z)).1.1
      dsimp [f,c];linarith
  let v (s : unitInterval × B) : ℝ × ℝ :=
    (1-s.1.val) • (r s.2).val + s.1.val • s.2.val.val
  have hvnorm (s : unitInterval × B) : ‖v s‖ ≤ 1 := by
    calc
      ‖v s‖ ≤ ‖(1-s.1.val) • (r s.2).val‖ + ‖s.1.val • s.2.val.val‖ := norm_add_le _ _
      _ = (1-s.1.val)*‖(r s.2).val‖ + s.1.val*‖s.2.val.val‖ := by
        rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.mpr s.1.property.2),abs_of_nonneg s.1.property.1]
      _ ≤ (1-s.1.val)*1 + s.1.val*1 := add_le_add
        (mul_le_mul_of_nonneg_left (hrect (r s.2)) (sub_nonneg.mpr s.1.property.2))
        (mul_le_mul_of_nonneg_left s.2.property s.1.property.1)
      _ = 1 := by ring
  have hvavoid (s : unitInterval × B) :
      v s ≠ ((-1/2 : ℝ),0) ∧ v s ≠ ((1/2 : ℝ),0) := by
    let side : Bool := if s.2.val.val.1 ≤ 0 then false else true
    let α : ℝ := (1-s.1.val)*‖g side s.2‖⁻¹+s.1.val
    have hd : 0 < ‖g side s.2‖ := norm_pos_iff.mpr (hg0 side s.2)
    have ha : 0 < α := by
      dsimp [α]
      by_cases ht : s.1.val=1
      · rw [ht];norm_num
      · exact add_pos_of_pos_of_nonneg
          (mul_pos (sub_pos.mpr (lt_of_le_of_ne s.1.property.2 ht)) (inv_pos.mpr hd)) s.1.property.1
    have hr : (r s.2).val=(c side+‖g side s.2‖⁻¹*(g side s.2).1/2,‖g side s.2‖⁻¹*(g side s.2).2) := by
      dsimp [r,f,u,side];split_ifs <;> rfl
    have hvx : (v s).1=c side+α*(s.2.val.val.1-c side) := by
      dsimp [v];rw [hr];dsimp [α,g];ring
    have hvy : (v s).2=α*s.2.val.val.2 := by
      dsimp [v];rw [hr];dsimp [α,g];ring
    have hsign := hrside s.2
    by_cases hs : s.2.val.val.1 ≤ 0
    · have hc : c side=(-1/2 : ℝ) := by simp [side,c,hs]
      rw [ite_eq_left hs] at hsign
      have hvle : (v s).1 ≤ 0 := by
        dsimp [v]
        exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr s.1.property.2) hsign)
          (mul_nonpos_of_nonneg_of_nonpos s.1.property.1 hs)
      constructor
      · intro h
        have hx := congrArg Prod.fst h
        have hy := congrArg Prod.snd h
        rw [hvx,hc] at hx
        rw [hvy] at hy
        apply s.2.val.property.1
        apply Prod.ext
        · dsimp at hx ⊢;nlinarith
        · dsimp at hy ⊢;exact (mul_eq_zero.mp hy).resolve_left ha.ne'
      · intro h;have hx := congrArg Prod.fst h;rw [hx] at hvle;norm_num at hvle
    · have hc : c side=(1/2 : ℝ) := by simp [side,c,hs]
      rw [ite_eq_right hs] at hsign
      have hvge : 0 ≤ (v s).1 := by
        dsimp [v]
        exact add_nonneg (mul_nonneg (sub_nonneg.mpr s.1.property.2) hsign)
          (mul_nonneg s.1.property.1 (le_of_not_ge hs))
      constructor
      · intro h;have hx := congrArg Prod.fst h;rw [hx] at hvge;norm_num at hvge
      · intro h
        have hx := congrArg Prod.fst h
        have hy := congrArg Prod.snd h
        rw [hvx,hc] at hx
        rw [hvy] at hy
        apply s.2.val.property.2
        apply Prod.ext
        · dsimp at hx ⊢;nlinarith
        · dsimp at hy ⊢;exact (mul_eq_zero.mp hy).resolve_left ha.ne'
  let H : (i.comp r).Homotopy (ContinuousMap.id B) := {
    toFun s := ⟨⟨v s,hvavoid s⟩,hvnorm s⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      have ht : Continuous (fun s : unitInterval × B => s.1.val) := continuous_subtype_val.comp continuous_fst
      exact ((continuous_const.sub ht).smul (continuous_subtype_val.comp (r.continuous.comp continuous_snd))).add
        (ht.smul (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)))
    map_zero_left z := by apply Subtype.ext;apply Subtype.ext;simp [v,i]
    map_one_left z := by apply Subtype.ext;apply Subtype.ext;simp [v] }
  have hri : r.comp i=ContinuousMap.id ActualSquareTheta := ContinuousMap.ext hfix
  let e : B ≃ₕ ActualSquareTheta := {
    toFun := r
    invFun := i
    left_inv := ⟨H⟩
    right_inv := by simpa only [hri] using ContinuousMap.Homotopic.refl (ContinuousMap.id ActualSquareTheta) }
  refine ⟨e,?_⟩
  intro z
  dsimp [e,r,f,u,g,c]
  split_ifs <;> rfl
end CurveComplex.Hyperbolic.PantsTheta
