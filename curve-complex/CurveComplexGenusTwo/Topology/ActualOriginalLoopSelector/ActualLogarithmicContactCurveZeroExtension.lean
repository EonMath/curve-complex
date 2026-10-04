import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualProductBoundedZeroExtension
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- A phase-contact time graph need not have a limit at the corner. Its actual
surface-coordinate trace nevertheless has a constructed continuous zero end,
using the original zero germ's endpoint norm bound. -/
theorem actual_logarithmic_contact_curve_zero_extension
    (g : C(unitInterval × unitInterval,ℂ)) (hg : ∀ τ,g (τ,0)=0)
    (Λ : C(unitInterval × Ioc (0:ℝ) 1,ℂ))
    (hΛ : ∀ z,Complex.exp (Λ z)=g
      (z.1,⟨z.2.val,z.2.property.1.le,z.2.property.2⟩))
    (γ : C(Ioc (0:ℝ) (1/2),unitInterval))
    (hγ : ∀ t,(Complex.exp ((1-(γ t:ℝ)) •
      Λ (0,⟨t.val,t.property.1,t.property.2.trans (by norm_num)⟩)+
      (γ t:ℝ) • Λ (1,⟨t.val,t.property.1,t.property.2.trans (by norm_num)⟩))).im=0) :
    ∃ C : C(Icc (0:ℝ) (1/2),ℂ), C ⟨0,le_rfl,by norm_num⟩=0 ∧
      (∀ t (ht : 0<t.val),C t=Complex.exp ((1-(γ ⟨t.val,ht,t.property.2⟩:ℝ)) •
        Λ (0,⟨t.val,ht,t.property.2.trans (by norm_num)⟩)+
        (γ ⟨t.val,ht,t.property.2⟩:ℝ) • Λ (1,⟨t.val,ht,t.property.2.trans (by norm_num)⟩))) ∧
      (∀ t,(C t).im=0) ∧ (∀ t,0<t.val → C t≠0) ∧
      (∀ t,‖C t‖ ≤ max ‖g (0,⟨t.val,t.property.1,t.property.2.trans (by norm_num)⟩)‖
        ‖g (1,⟨t.val,t.property.1,t.property.2.trans (by norm_num)⟩)‖) := by
  let f : C(Unit × Ioc (0:ℝ) (1/2),ℂ) :=
    ⟨fun z => Complex.exp ((1-(γ z.2:ℝ)) •
      Λ (0,⟨z.2.val,z.2.property.1,z.2.property.2.trans (by norm_num)⟩)+
      (γ z.2:ℝ) • Λ (1,⟨z.2.val,z.2.property.1,z.2.property.2.trans (by norm_num)⟩)),by fun_prop⟩
  let B : C(Unit × Icc (0:ℝ) (1/2),ℝ) :=
    ⟨fun z => max ‖g (0,⟨z.2.val,z.2.property.1,z.2.property.2.trans (by norm_num)⟩)‖
      ‖g (1,⟨z.2.val,z.2.property.1,z.2.property.2.trans (by norm_num)⟩)‖,by fun_prop⟩
  have hB (x : Unit) : B (x,⟨0,le_rfl,by norm_num⟩)=0 := by
    change max ‖g (0,0)‖ ‖g (1,0)‖=0
    rw [hg,hg]; simp
  have hbound (z : Unit × Ioc (0:ℝ) (1/2)) :
      ‖f z‖≤B (z.1,⟨z.2.val,z.2.property.1.le,z.2.property.2⟩) := by
    have hh := actual_complex_log_affine_norm_le
      (Λ (0,⟨z.2.val,z.2.property.1,z.2.property.2.trans (by norm_num)⟩))
      (Λ (1,⟨z.2.val,z.2.property.1,z.2.property.2.trans (by norm_num)⟩)) (γ z.2)
    rw [hΛ,hΛ] at hh
    exact hh
  obtain ⟨E,hEzero,hEpos⟩ := actual_product_bounded_zero_extension (1/2) (by norm_num) f B hB hbound
  let C : C(Icc (0:ℝ) (1/2),ℂ) := ⟨fun t => E ((),t),by fun_prop⟩
  have hzero : C ⟨0,le_rfl,by norm_num⟩=0 := hEzero ()
  have hpos (t : Icc (0:ℝ) (1/2)) (ht : 0<t.val) : C t=f ((),⟨t.val,ht,t.property.2⟩) :=
    hEpos ((),t) ht
  refine ⟨C,hzero,hpos,?_,?_,?_⟩
  · intro t
    by_cases ht : 0<t.val
    · rw [hpos t ht]; exact hγ ⟨t.val,ht,t.property.2⟩
    · have hz : t=⟨0,le_rfl,by norm_num⟩ :=
        Subtype.ext (le_antisymm (le_of_not_gt ht) t.property.1)
      rw [hz,hzero]; rfl
  · intro t ht
    rw [hpos t ht]
    exact Complex.exp_ne_zero _
  · intro t
    by_cases ht : 0<t.val
    · rw [hpos t ht]
      exact hbound ((),⟨t.val,ht,t.property.2⟩)
    · have hz : t=⟨0,le_rfl,by norm_num⟩ :=
        Subtype.ext (le_antisymm (le_of_not_gt ht) t.property.1)
      subst t
      change ‖C ⟨0,le_rfl,by norm_num⟩‖ ≤ max ‖g (0,0)‖ ‖g (1,0)‖
      rw [hzero,hg,hg]; simp
end CurveComplex.HyperellipticModel
