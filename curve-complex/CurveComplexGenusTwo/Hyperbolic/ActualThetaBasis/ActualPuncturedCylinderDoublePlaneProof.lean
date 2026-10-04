import CurveComplexGenusTwo.Hyperbolic.ActualThetaBasis.HaasActualPantsDefinitions
open Set Topology
namespace CurveComplex.Hyperbolic
theorem actual_punctured_cylinder_double_punctured_plane_homeomorph : ∃ e : ActualPuncturedCylinder ≃ₜ {z : ℂ // z ≠ 0 ∧ z ≠ 1},
    (∀ z, (e z).val=(Real.exp z.val.2 : ℂ)*(z.val.1 : ℂ)) ∧
    (e actualPantsBase).val = -1 := by
  have hWhole : ∃ e : (Circle × ℝ) ≃ₜ {z : ℂ // z ≠ 0},
      ∀ z, (e z).val = (Real.exp z.2 : ℂ) * (z.1 : ℂ) := by
    have hnorm (z : Circle × ℝ) : ‖(Real.exp z.2 : ℂ) * (z.1 : ℂ)‖=Real.exp z.2 := by
      rw [norm_mul,Complex.norm_real,Circle.norm_coe,mul_one,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    let e : (Circle × ℝ) ≃ₜ {z : ℂ // z ≠ 0} := {
      toFun z := ⟨(Real.exp z.2 : ℂ) * (z.1 : ℂ),
        mul_ne_zero (by exact_mod_cast Real.exp_ne_zero z.2) z.1.coe_ne_zero⟩
      invFun z := (⟨z.val / (‖z.val‖ : ℂ),by
        simp only [Submonoid.unitSphere,Subsemigroup.mem_mk,Submonoid.mem_mk,mem_sphere_zero_iff_norm]
        rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_norm]
        exact div_self (norm_ne_zero_iff.mpr z.property)⟩,Real.log ‖z.val‖)
      left_inv z := by
        apply Prod.ext
        · apply Subtype.ext
          change ((Real.exp z.2 : ℂ) * (z.1 : ℂ)) / (‖(Real.exp z.2 : ℂ) * (z.1 : ℂ)‖ : ℂ) = _
          rw [hnorm]
          exact mul_div_cancel_left₀ _ (by exact_mod_cast Real.exp_ne_zero z.2)
        · change Real.log ‖(Real.exp z.2 : ℂ) * (z.1 : ℂ)‖=z.2
          rw [hnorm,Real.log_exp]
      right_inv z := by
        apply Subtype.ext
        change (Real.exp (Real.log ‖z.val‖) : ℂ) * (z.val / (‖z.val‖ : ℂ))=z.val
        rw [Real.exp_log (norm_pos_iff.mpr z.property)]
        exact mul_div_cancel₀ _ (by exact_mod_cast norm_ne_zero_iff.mpr z.property)
      continuous_toFun := by fun_prop
      continuous_invFun := by
        apply Continuous.prodMk
        · apply Continuous.subtype_mk
          exact continuous_subtype_val.div (Complex.continuous_ofReal.comp (continuous_norm.comp continuous_subtype_val))
            (fun z => by exact_mod_cast norm_ne_zero_iff.mpr z.property)
        · exact (continuous_norm.comp continuous_subtype_val).log
            (fun z => norm_ne_zero_iff.mpr z.property) }
    exact ⟨e,fun z=>rfl⟩
  obtain ⟨e, he⟩ := hWhole
  have hunit : (e ((1 : Circle),0)).val=(1 : ℂ) := by simp [he]
  have ha (z : Circle × ℝ) : (e z).val=1 ↔ z=((1 : Circle),0) := by
    constructor
    · intro hz
      apply e.injective
      exact Subtype.ext (hz.trans hunit.symm)
    · rintro rfl
      exact hunit
  let r : ActualPuncturedCylinder ≃ₜ {z : {w : ℂ // w ≠ 0} // z.val ≠ 1} :=
    e.subtype (fun z => (not_congr (ha z)).symm)
  let d : {z : {w : ℂ // w ≠ 0} // z.val ≠ 1} ≃ₜ {z : ℂ // z ≠ 0 ∧ z ≠ 1} := {
    toFun z := ⟨z.val.val,⟨z.val.property,z.property⟩⟩
    invFun z := ⟨⟨z.val,z.property.1⟩,z.property.2⟩
    left_inv _ := rfl
    right_inv _ := rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  refine ⟨r.trans d,?_,?_⟩
  · intro z
    exact he z.val
  · change (e actualPantsBase.val).val = -1
    simp [he,actualPantsBase]
end CurveComplex.Hyperbolic
