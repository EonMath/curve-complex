import CurveComplexGenusTwo.Hyperbolic.ActualThetaBasis.ActualDoublePunctureRectangleDeformationProof
import CurveComplexGenusTwo.Hyperbolic.ActualThetaBasis.ActualRectangleThetaDeformationProof
open Set Topology ContinuousMap
namespace CurveComplex.Hyperbolic.PantsTheta
theorem actual_radial_negative_axis_and_theta_fixing :
    let P := {z : ℝ×ℝ // z≠((-1/2:ℝ),0) ∧ z≠((1/2:ℝ),0)}
    ∃ e : P ≃ₕ ActualSquareTheta,
      (∀ (a : ℝ),0<a → ∀ (z : P),z.val=(-a-1/2,0) → e z=thetaBase) ∧
      (∀ (z : ActualSquareTheta) (p : P),p.val=z.val → e p=z) := by
  intro P
  obtain ⟨clamp,hclamp⟩ := actual_double_puncture_rectangle_deformation
  obtain ⟨radial,hradial⟩ := actual_rectangle_theta_deformation
  refine ⟨clamp.trans radial,?_,?_⟩
  · intro a ha z hz
    have hx : ((clamp z).val.val).1 < -1/2 := by
      rw [hclamp,hz]
      change (max 1 ‖(-a-1/2,(0:ℝ))‖)⁻¹*(-a-1/2)< -1/2
      have hab : |-a-1/2|=a+1/2 := by rw [abs_of_neg (by linarith)];ring
      rw [Prod.norm_mk,Real.norm_eq_abs,hab,norm_zero,max_eq_left (by linarith : (0:ℝ)≤a+1/2)]
      by_cases hd : a+1/2 ≤ 1
      · rw [max_eq_left hd];norm_num;linarith
      · rw [max_eq_right (le_of_not_ge hd)]
        have he : a+1/2≠0 := by linarith
        field_simp
        linarith
    have hy : (clamp z).val.val.2=0 := by rw [hclamp,hz];simp
    apply Subtype.ext
    change (radial (clamp z)).val=thetaBase.val
    rw [hradial]
    have hx0 : (clamp z).val.val.1 ≤ 0 := by linarith
    rw [ite_eq_left hx0]
    dsimp only
    rw [hy]
    have hw : 2*((clamp z).val.val.1-(-1/2))<0 := by linarith
    have hn : ‖(2*((clamp z).val.val.1-(-1/2)),(0:ℝ))‖ = -(2*((clamp z).val.val.1-(-1/2))) := by
      rw [Prod.norm_mk,Real.norm_eq_abs,norm_zero,abs_of_neg hw,max_eq_left (by linarith)]
    rw [hn]
    apply Prod.ext
    · dsimp [thetaBase]
      rw [inv_neg,neg_mul,inv_mul_cancel₀ (ne_of_lt hw)]
      norm_num
    · simp [thetaBase]
  · intro z p hp
    have hn : ‖z.val‖ ≤ 1 := by
      apply norm_prod_le_iff.mpr
      rcases z.property with h|h
      · exact ⟨by simpa [Real.norm_eq_abs] using abs_le.mpr h.1,
          by rcases h.2 with h|h <;> simp [h]⟩
      · exact ⟨by rcases h.1 with h|h|h <;> simp [h],
          by simpa [Real.norm_eq_abs] using abs_le.mpr h.2⟩
    have hc : (clamp p).val.val=z.val := by rw [hclamp,hp,max_eq_left hn];simp
    have hbounds : (-1 ≤ z.val.1 ∧ z.val.1 ≤ 1) ∧ (-1 ≤ z.val.2 ∧ z.val.2 ≤ 1) := by
      exact ⟨abs_le.mp (by simpa [Real.norm_eq_abs] using (norm_fst_le z.val).trans hn),
        abs_le.mp (by simpa [Real.norm_eq_abs] using (norm_snd_le z.val).trans hn)⟩
    have hD (c : ℝ) (hc' : c=-1/2 ∨ c=1/2)
        (hs : if c=-1/2 then z.val.1 ≤ 0 else 0 ≤ z.val.1) : ‖(2*(z.val.1-c),z.val.2)‖=1 := by
      rcases hc' with rfl|rfl
      · have hs' : z.val.1 ≤ 0 := by simpa using hs
        have hw : |2*(z.val.1-(-1/2))| ≤ 1 := abs_le.mpr ⟨by linarith [hbounds.1.1],by linarith⟩
        have hv : |z.val.2| ≤ 1 := abs_le.mpr hbounds.2
        change max |2*(z.val.1-(-1/2))| |z.val.2|=1
        rcases z.property with h|h
        · rcases h.2 with h|h <;> simp only [h,abs_neg,abs_one] <;> exact max_eq_right hw
        · rcases h.1 with h|h|h
          · rw [h];norm_num [max_eq_left hv]
          · rw [h];norm_num [max_eq_left hv]
          · linarith
      · have hs' : 0 ≤ z.val.1 := by norm_num at hs;exact hs
        have hw : |2*(z.val.1-(1/2))| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith [hbounds.1.2]⟩
        have hv : |z.val.2| ≤ 1 := abs_le.mpr hbounds.2
        change max |2*(z.val.1-(1/2))| |z.val.2|=1
        rcases z.property with h|h
        · rcases h.2 with h|h <;> simp only [h,abs_neg,abs_one] <;> exact max_eq_right hw
        · rcases h.1 with h|h|h
          · linarith
          · rw [h];norm_num [max_eq_left hv]
          · rw [h];norm_num [max_eq_left hv]
    apply Subtype.ext
    change (radial (clamp p)).val=z.val
    rw [hradial,hc]
    by_cases hs : z.val.1 ≤ 0
    · rw [ite_eq_left hs]
      dsimp only
      rw [hD (-1/2) (Or.inl rfl) (by simpa using hs)]
      apply Prod.ext <;> dsimp <;> ring
    · rw [ite_eq_right hs]
      dsimp only
      rw [hD (1/2) (Or.inr rfl) (by norm_num;exact le_of_not_ge hs)]
      apply Prod.ext <;> dsimp <;> ring
end CurveComplex.Hyperbolic.PantsTheta
