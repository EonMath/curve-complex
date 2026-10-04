import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualEndpointInnerCutoff
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- An actual supported log patch: the outer seam and both time boundaries
are literal source coordinates; the inner half is the finite phase redraw.
Joint continuity at the zero endpoint is constructed, not assumed. -/
theorem actual_supported_logarithmic_germ_patch
    (g : C(unitInterval × unitInterval,ℂ)) (hg : ∀ τ,g (τ,0)=0)
    (Λ : C(unitInterval × Ioc (0:ℝ) 1,ℂ))
    (hΛ : ∀ z, Complex.exp (Λ z)=g
      (z.1,⟨z.2.val,z.2.property.1.le,z.2.property.2⟩)) :
    ∃ c : C(unitInterval,unitInterval),
    ∃ H : C((unitInterval × unitInterval) × unitInterval,ℂ),
      (∀ t : unitInterval, (t:ℝ)≤1/2 → c t=1) ∧ c 1=0 ∧
      (∀ s τ,H ((s,τ),0)=0) ∧
      (∀ τ t,H ((0,τ),t)=g (τ,t)) ∧
      (∀ s τ,H ((s,τ),1)=g (τ,1)) ∧
      (∀ s t,H ((s,0),t)=g (0,t) ∧ H ((s,1),t)=g (1,t)) ∧
      (∀ (τ t : unitInterval) (ht : 0<(t:ℝ)), (t:ℝ)≤1/2 →
        H ((1,τ),t)=Complex.exp ((1-(τ:ℝ)) • Λ (0,⟨t.val,ht,t.property.2⟩)+
          (τ:ℝ) • Λ (1,⟨t.val,ht,t.property.2⟩))) ∧
      (∀ s τ t, ‖H ((s,τ),t)‖ ≤ max ‖g (τ,t)‖ (max ‖g (0,t)‖ ‖g (1,t)‖)) ∧
      (∀ (s τ t : unitInterval), 0<(t:ℝ) → H ((s,τ),t)≠0) := by
  obtain ⟨c,hcinner,hcouter⟩ := actual_endpoint_inner_cutoff 1 (by norm_num)
  let f : C((unitInterval × unitInterval) × Ioc (0:ℝ) 1,ℂ) :=
    ⟨fun z => Complex.exp
      ((1-(z.1.1:ℝ)*(c ⟨z.2.val,z.2.property.1.le,z.2.property.2⟩:ℝ)) • Λ (z.1.2,z.2)+
        ((z.1.1:ℝ)*(c ⟨z.2.val,z.2.property.1.le,z.2.property.2⟩:ℝ)) •
          ((1-(z.1.2:ℝ)) • Λ (0,z.2)+(z.1.2:ℝ) • Λ (1,z.2))),by fun_prop⟩
  let B : C((unitInterval × unitInterval) × unitInterval,ℝ) :=
    ⟨fun z => max ‖g (z.1.2,z.2)‖ (max ‖g (0,z.2)‖ ‖g (1,z.2)‖),by fun_prop⟩
  have hB (x : unitInterval × unitInterval) : B (x,⟨0,le_rfl,(by norm_num)⟩)=0 := by
    change max ‖g (x.2,0)‖ (max ‖g (0,0)‖ ‖g (1,0)‖)=0
    rw [hg,hg,hg]
    simp
  have hbound (z : (unitInterval × unitInterval) × Ioc (0:ℝ) 1) :
      ‖f z‖≤B (z.1,⟨z.2.val,z.2.property.1.le,z.2.property.2⟩) := by
    let t : unitInterval := ⟨z.2.val,z.2.property.1.le,z.2.property.2⟩
    let w : unitInterval := ⟨(z.1.1:ℝ)*(c t:ℝ),
      mul_nonneg z.1.1.property.1 (c t).property.1,by
        have hh := mul_le_mul_of_nonneg_left (c t).property.2 z.1.1.property.1
        nlinarith [z.1.1.property.2]⟩
    have hb := actual_complex_log_affine_norm_le (Λ (0,z.2)) (Λ (1,z.2)) z.1.2
    rw [hΛ,hΛ] at hb
    have hh := actual_complex_log_affine_norm_le (Λ (z.1.2,z.2))
      ((1-(z.1.2:ℝ)) • Λ (0,z.2)+(z.1.2:ℝ) • Λ (1,z.2)) w
    apply hh.trans
    apply max_le
    · rw [hΛ]
      exact le_max_left _ _
    · exact hb.trans (le_max_right _ _)
  obtain ⟨H,hHzero,hHpos⟩ := actual_product_bounded_zero_extension 1 (by norm_num) f B hB hbound
  have hzero (s τ : unitInterval) : H ((s,τ),0)=0 := hHzero (s,τ)
  have hcinner' (t : unitInterval) (ht : (t:ℝ)≤1/2) : c t=1 := hcinner t ht
  have hcouter' : c 1=0 := hcouter
  refine ⟨c,H,hcinner',hcouter',?_,?_,?_,?_,?_,?_,?_⟩
  · intro s τ; exact hHzero (s,τ)
  · intro τ t
    by_cases ht : 0<(t:ℝ)
    · rw [hHpos ((0,τ),t) ht]
      simpa [f] using hΛ (τ,⟨t.val,ht,t.property.2⟩)
    · have hz : t=0 := Subtype.ext (le_antisymm (le_of_not_gt ht) t.property.1)
      subst t; rw [hzero,hg]
  · intro s τ
    rw [hHpos ((s,τ),1) (by norm_num)]
    change Complex.exp ((1-(s:ℝ)*(c 1:ℝ)) • Λ (τ,⟨(1:unitInterval).val,by norm_num,(1:unitInterval).property.2⟩)+
      ((s:ℝ)*(c 1:ℝ)) • ((1-(τ:ℝ)) • Λ (0,⟨(1:unitInterval).val,by norm_num,(1:unitInterval).property.2⟩)+
        (τ:ℝ) • Λ (1,⟨(1:unitInterval).val,by norm_num,(1:unitInterval).property.2⟩)))=g (τ,1)
    rw [hcouter']
    change Complex.exp ((1-(s:ℝ)*0) • Λ (τ,⟨(1:unitInterval).val,by norm_num,(1:unitInterval).property.2⟩)+
      ((s:ℝ)*0) • ((1-(τ:ℝ)) • Λ (0,⟨(1:unitInterval).val,by norm_num,(1:unitInterval).property.2⟩)+
        (τ:ℝ) • Λ (1,⟨(1:unitInterval).val,by norm_num,(1:unitInterval).property.2⟩)))=g (τ,1)
    rw [mul_zero,sub_zero,one_smul,zero_smul,add_zero]
    exact hΛ (τ,⟨(1:unitInterval).val,by norm_num,(1:unitInterval).property.2⟩)

  · intro s t
    by_cases ht : 0<(t:ℝ)
    · rw [hHpos ((s,0),t) ht,hHpos ((s,1),t) ht]
      constructor
      · change Complex.exp ((1-(s:ℝ)*(c t:ℝ)) • Λ (0,⟨t.val,ht,t.property.2⟩)+
          ((s:ℝ)*(c t:ℝ)) • ((1-(0:ℝ)) • Λ (0,⟨t.val,ht,t.property.2⟩)+
            (0:ℝ) • Λ (1,⟨t.val,ht,t.property.2⟩)))=g (0,t)
        rw [sub_zero,one_smul,zero_smul,add_zero,← add_smul]
        simp only [sub_add_cancel,one_smul]
        exact hΛ (0,⟨t.val,ht,t.property.2⟩)
      · change Complex.exp ((1-(s:ℝ)*(c t:ℝ)) • Λ (1,⟨t.val,ht,t.property.2⟩)+
          ((s:ℝ)*(c t:ℝ)) • ((1-(1:ℝ)) • Λ (0,⟨t.val,ht,t.property.2⟩)+
            (1:ℝ) • Λ (1,⟨t.val,ht,t.property.2⟩)))=g (1,t)
        rw [sub_self,zero_smul,one_smul,zero_add,← add_smul]
        simp only [sub_add_cancel,one_smul]
        exact hΛ (1,⟨t.val,ht,t.property.2⟩)
    · have hz : t=0 := Subtype.ext (le_antisymm (le_of_not_gt ht) t.property.1)
      subst t; simp only [hzero,hg,and_self]
  · intro τ t ht hhalf
    rw [hHpos ((1,τ),t) ht]
    simp [f,hcinner' t hhalf]
  · intro s τ t
    by_cases ht : 0<(t:ℝ)
    · rw [hHpos ((s,τ),t) ht]
      exact hbound ((s,τ),⟨t.val,ht,t.property.2⟩)
    · have hz : t=0 := Subtype.ext (le_antisymm (le_of_not_gt ht) t.property.1)
      subst t
      simp only [hzero,hg,norm_zero,max_self,le_refl]
  · intro s τ t ht
    rw [hHpos ((s,τ),t) ht]
    exact Complex.exp_ne_zero _
end CurveComplex.HyperellipticModel
