import CurveComplexGenusTwo.Hyperbolic.ActualThetaBasis.ActualSquareThetaCover
open Set Topology ContinuousMap
namespace CurveComplex.Hyperbolic.PantsTheta
theorem actual_double_puncture_rectangle_deformation :
    let P := {z : ℝ × ℝ // z ≠ ((-1/2 : ℝ),0) ∧ z ≠ ((1/2 : ℝ),0)}
    ∃ r : P ≃ₕ {z : P // ‖z.val‖ ≤ 1},
      ∀ z, (r z).val.val = (max 1 ‖z.val‖)⁻¹ • z.val := by
  intro P
  let d (z : P) : ℝ := max 1 ‖z.val‖
  have hd (z : P) : 0 < d z := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let f (z : P) : ℝ × ℝ := (d z)⁻¹ • z.val
  have hn (z : P) : ‖f z‖=‖z.val‖ / d z := by
    simp only [f,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (hd z)),div_eq_inv_mul]
  have hle (z : P) : ‖f z‖ ≤ 1 := by
    rw [hn,div_le_iff₀ (hd z),one_mul]
    exact le_max_right _ _
  have hstay (z : P) : f z ≠ ((-1/2 : ℝ),0) ∧ f z ≠ ((1/2 : ℝ),0) := by
    by_cases hz : ‖z.val‖ ≤ 1
    · have hf : f z=z.val := by simp [f,d,max_eq_left hz]
      simpa [hf] using z.property
    · have hn1 : ‖f z‖=1 := by
        rw [hn,show d z=‖z.val‖ from max_eq_right (le_of_not_ge hz)]
        exact div_self (ne_of_gt (lt_trans zero_lt_one (lt_of_not_ge hz)))
      constructor <;> intro he <;> rw [he] at hn1 <;> norm_num at hn1
  let r : C(P,{z : P // ‖z.val‖ ≤ 1}) := {
    toFun z := ⟨⟨f z,hstay z⟩,hle z⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact ((continuous_const.max (continuous_norm.comp continuous_subtype_val)).inv₀
        (fun z => (hd z).ne')).smul continuous_subtype_val }
  let B := {z : P // ‖z.val‖ ≤ 1}
  let i : C(B,P) := ⟨Subtype.val,continuous_subtype_val⟩
  let W (s : unitInterval × P) : ℝ := (1-s.1.val)/(d s.2)+s.1.val
  have hW (s : unitInterval × P) : 0 ≤ W s := by
    exact add_nonneg (div_nonneg (sub_nonneg.mpr s.1.property.2) (hd s.2).le) s.1.property.1
  have hmove (s : unitInterval × P) :
      W s • s.2.val ≠ ((-1/2 : ℝ),0) ∧ W s • s.2.val ≠ ((1/2 : ℝ),0) := by
    by_cases hz : ‖s.2.val‖ ≤ 1
    · have hw : W s=1 := by dsimp [W,d];rw [max_eq_left hz];ring
      simpa [hw] using s.2.property
    · have hnLower : 1 ≤ ‖W s • s.2.val‖ := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hW s)]
        have hdEq : d s.2=‖s.2.val‖ := max_eq_right (le_of_not_ge hz)
        dsimp [W]
        rw [hdEq,add_mul,div_mul_cancel₀ _ (ne_of_gt (lt_trans zero_lt_one (lt_of_not_ge hz)))]
        nlinarith [mul_nonneg s.1.property.1 (sub_nonneg.mpr (le_of_not_ge hz))]
      constructor <;> intro he <;> rw [he] at hnLower <;> norm_num at hnLower
  let H : (i.comp r).Homotopy (ContinuousMap.id P) := {
    toFun s := ⟨W s • s.2.val,hmove s⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      have hw : Continuous W := by
        exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).div
          (continuous_const.max (continuous_norm.comp (continuous_subtype_val.comp continuous_snd)))
          (fun s => (hd s.2).ne')).add (continuous_subtype_val.comp continuous_fst)
      exact hw.smul (continuous_subtype_val.comp continuous_snd)
    map_zero_left z := by apply Subtype.ext;simp [W,i,r,f,div_eq_inv_mul]
    map_one_left z := by apply Subtype.ext;simp [W] }
  have hri : r.comp i=ContinuousMap.id B := by
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    apply Subtype.ext
    change f z.val=z.val.val
    simp [f,d,max_eq_left z.property]
  let e : P ≃ₕ B := {
    toFun := r
    invFun := i
    left_inv := ⟨H⟩
    right_inv := by simpa only [hri] using ContinuousMap.Homotopic.refl (ContinuousMap.id B) }
  exact ⟨e,fun z=>rfl⟩
end CurveComplex.Hyperbolic.PantsTheta
