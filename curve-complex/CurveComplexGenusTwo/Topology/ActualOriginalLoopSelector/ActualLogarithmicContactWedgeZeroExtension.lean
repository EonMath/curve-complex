import CurveComplexGenusTwo.Topology.ActualOriginalLoopSelector.ActualLogarithmicContactCurveZeroExtension
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- The actual region below a phase-contact time graph has a jointly
continuous zero-corner filling, even without a limit of the time graph. -/
theorem actual_logarithmic_contact_wedge_zero_extension
    (g : C(unitInterval × unitInterval,ℂ)) (hg : ∀ τ,g (τ,0)=0)
    (Λ : C(unitInterval × Ioc (0:ℝ) 1,ℂ))
    (hΛ : ∀ z,Complex.exp (Λ z)=g
      (z.1,⟨z.2.val,z.2.property.1.le,z.2.property.2⟩))
    (γ : C(Ioc (0:ℝ) (1/2),unitInterval))
    (hγ : ∀ t,(Complex.exp ((1-(γ t:ℝ)) •
      Λ (0,⟨t.val,t.property.1,t.property.2.trans (by norm_num)⟩)+
      (γ t:ℝ) • Λ (1,⟨t.val,t.property.1,t.property.2.trans (by norm_num)⟩))).im=0) :
    ∃ F : C(unitInterval × Icc (0:ℝ) (1/2),ℂ),
      (∀ s,F (s,⟨0,le_rfl,by norm_num⟩)=0) ∧
      (∀ (s : unitInterval) t (ht : 0<t.val),F (s,t)=Complex.exp
        ((1-(s:ℝ)*(γ ⟨t.val,ht,t.property.2⟩:ℝ)) •
          Λ (0,⟨t.val,ht,t.property.2.trans (by norm_num)⟩)+
          ((s:ℝ)*(γ ⟨t.val,ht,t.property.2⟩:ℝ)) •
          Λ (1,⟨t.val,ht,t.property.2.trans (by norm_num)⟩))) ∧
      (∀ t,F (0,t)=g (0,⟨t.val,t.property.1,t.property.2.trans (by norm_num)⟩)) ∧
      (∀ t,(F (1,t)).im=0) ∧
      (∀ s t,0<t.val → F (s,t)≠0) ∧
      (∀ s t,‖F (s,t)‖ ≤ max ‖g (0,⟨t.val,t.property.1,t.property.2.trans (by norm_num)⟩)‖
        ‖g (1,⟨t.val,t.property.1,t.property.2.trans (by norm_num)⟩)‖) := by
  let f : C(unitInterval × Ioc (0:ℝ) (1/2),ℂ) :=
    ⟨fun z => Complex.exp ((1-(z.1:ℝ)*(γ z.2:ℝ)) •
      Λ (0,⟨z.2.val,z.2.property.1,z.2.property.2.trans (by norm_num)⟩)+
      ((z.1:ℝ)*(γ z.2:ℝ)) •
        Λ (1,⟨z.2.val,z.2.property.1,z.2.property.2.trans (by norm_num)⟩)),by fun_prop⟩
  let B : C(unitInterval × Icc (0:ℝ) (1/2),ℝ) :=
    ⟨fun z => max ‖g (0,⟨z.2.val,z.2.property.1,z.2.property.2.trans (by norm_num)⟩)‖
      ‖g (1,⟨z.2.val,z.2.property.1,z.2.property.2.trans (by norm_num)⟩)‖,by fun_prop⟩
  have hB (s : unitInterval) : B (s,⟨0,le_rfl,by norm_num⟩)=0 := by
    change max ‖g (0,0)‖ ‖g (1,0)‖=0
    rw [hg,hg]; simp
  have hbound (z : unitInterval × Ioc (0:ℝ) (1/2)) :
      ‖f z‖≤B (z.1,⟨z.2.val,z.2.property.1.le,z.2.property.2⟩) := by
    let w : unitInterval := ⟨(z.1:ℝ)*(γ z.2:ℝ),mul_nonneg z.1.property.1 (γ z.2).property.1,
      (mul_le_mul_of_nonneg_left (γ z.2).property.2 z.1.property.1).trans (by simpa using z.1.property.2)⟩
    have hh := actual_complex_log_affine_norm_le
      (Λ (0,⟨z.2.val,z.2.property.1,z.2.property.2.trans (by norm_num)⟩))
      (Λ (1,⟨z.2.val,z.2.property.1,z.2.property.2.trans (by norm_num)⟩)) w
    rw [hΛ,hΛ] at hh
    exact hh
  obtain ⟨F,hFzero,hFpos⟩ := actual_product_bounded_zero_extension (1/2) (by norm_num) f B hB hbound
  have hpos (s : unitInterval) (t : Icc (0:ℝ) (1/2)) (ht : 0<t.val) :
      F (s,t)=f (s,⟨t.val,ht,t.property.2⟩) := hFpos (s,t) ht
  refine ⟨F,hFzero,hpos,?_,?_,?_,?_⟩
  · intro t
    by_cases ht : 0<t.val
    · rw [hpos 0 t ht]
      simpa [f] using hΛ (0,⟨t.val,ht,t.property.2.trans (by norm_num)⟩)
    · have hz : t=⟨0,le_rfl,by norm_num⟩ :=
        Subtype.ext (le_antisymm (le_of_not_gt ht) t.property.1)
      subst t
      change F (0,⟨0,le_rfl,by norm_num⟩)=g (0,0)
      rw [hFzero,hg]
  · intro t
    by_cases ht : 0<t.val
    · rw [hpos 1 t ht]
      change (Complex.exp ((1-(1:ℝ)*(γ ⟨t.val,ht,t.property.2⟩:ℝ)) •
        Λ (0,⟨t.val,ht,t.property.2.trans (by norm_num)⟩)+
        ((1:ℝ)*(γ ⟨t.val,ht,t.property.2⟩:ℝ)) •
          Λ (1,⟨t.val,ht,t.property.2.trans (by norm_num)⟩))).im=0
      rw [one_mul]
      exact hγ ⟨t.val,ht,t.property.2⟩
    · have hz : t=⟨0,le_rfl,by norm_num⟩ :=
        Subtype.ext (le_antisymm (le_of_not_gt ht) t.property.1)
      rw [hz,hFzero]; rfl
  · intro s t ht
    rw [hpos s t ht]
    exact Complex.exp_ne_zero _
  · intro s t
    by_cases ht : 0<t.val
    · rw [hpos s t ht]
      exact hbound (s,⟨t.val,ht,t.property.2⟩)
    · have hz : t=⟨0,le_rfl,by norm_num⟩ :=
        Subtype.ext (le_antisymm (le_of_not_gt ht) t.property.1)
      subst t
      change ‖F (s,⟨0,le_rfl,by norm_num⟩)‖ ≤ max ‖g (0,0)‖ ‖g (1,0)‖
      rw [hFzero,hg,hg]; simp
end CurveComplex.HyperellipticModel
