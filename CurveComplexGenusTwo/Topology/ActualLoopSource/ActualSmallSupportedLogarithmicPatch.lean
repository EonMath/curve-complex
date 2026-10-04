import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSupportedLogarithmicGermPatch
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- The actual zero germ selects its own small window and constructs a
supported logarithmic patch entirely within the complex unit ball. -/
theorem actual_small_supported_logarithmic_patch
    (g : C(unitInterval × unitInterval,ℂ)) (hg : ∀ τ,g (τ,0)=0)
    (Λ : C(unitInterval × Ioc (0:ℝ) 1,ℂ))
    (hΛ : ∀ z, Complex.exp (Λ z)=g
      (z.1,⟨z.2.val,z.2.property.1.le,z.2.property.2⟩)) :
    ∃ d : ℝ, ∃ _hd : 0<d, ∃ _hh : d<1/2,
    ∃ l : C(unitInterval,unitInterval), ∃ lp : C(Ioc (0:ℝ) 1,Ioc (0:ℝ) 1),
      (∀ t, (l t:ℝ)=d*(t:ℝ)) ∧ (∀ t, (lp t).val=d*t.val) ∧
    ∃ H : C((unitInterval × unitInterval) × unitInterval,ℂ),
      (∀ s τ,H ((s,τ),0)=0) ∧
      (∀ τ t,H ((0,τ),t)=g (τ,l t)) ∧
      (∀ s τ,H ((s,τ),1)=g (τ,l 1)) ∧
      (∀ s t,H ((s,0),t)=g (0,l t) ∧ H ((s,1),t)=g (1,l t)) ∧
      (∀ (τ t : unitInterval) (ht : 0<(t:ℝ)), (t:ℝ)≤1/2 →
        H ((1,τ),t)=Complex.exp ((1-(τ:ℝ)) • Λ (0,lp ⟨t.val,ht,t.property.2⟩)+
          (τ:ℝ) • Λ (1,lp ⟨t.val,ht,t.property.2⟩))) ∧
      (∀ s τ t, ‖H ((s,τ),t)‖<1) ∧
      (∀ (s τ t : unitInterval), 0<(t:ℝ) → H ((s,τ),t)≠0) := by
  obtain ⟨d,hd,hh,hsmall⟩ := actual_uniform_zero_germ_smallness g hg 1 (by norm_num)
  have hd1 : d≤1 := (hh.trans (by norm_num)).le
  let l : C(unitInterval,unitInterval) :=
    ⟨fun t => ⟨d*(t:ℝ),mul_nonneg hd.le t.property.1,by
      have he := mul_le_mul_of_nonneg_left t.property.2 hd.le
      nlinarith⟩,by fun_prop⟩
  let lp : C(Ioc (0:ℝ) 1,Ioc (0:ℝ) 1) :=
    ⟨fun t => ⟨d*t.val,mul_pos hd t.property.1,by
      have he := mul_le_mul_of_nonneg_left t.property.2 hd.le
      nlinarith⟩,by fun_prop⟩
  let gd : C(unitInterval × unitInterval,ℂ) := ⟨fun z => g (z.1,l z.2),by fun_prop⟩
  let Λd : C(unitInterval × Ioc (0:ℝ) 1,ℂ) := ⟨fun z => Λ (z.1,lp z.2),by fun_prop⟩
  have hlzero : l 0=0 := by apply Subtype.ext; simp [l]
  have hgd (τ : unitInterval) : gd (τ,0)=0 := by
    change g (τ,l 0)=0
    rw [hlzero,hg]
  have hΛd (z : unitInterval × Ioc (0:ℝ) 1) :
      Complex.exp (Λd z)=gd (z.1,⟨z.2.val,z.2.property.1.le,z.2.property.2⟩) := by
    exact hΛ (z.1,lp z.2)
  obtain ⟨c,H,_,_,hzero,hstart,houter,hboundary,hinner,hnorm,hnz⟩ :=
    actual_supported_logarithmic_germ_patch gd hgd Λd hΛd
  refine ⟨d,hd,hh,l,lp,(fun _ => rfl),(fun _ => rfl),H,hzero,hstart,houter,hboundary,hinner,?_,hnz⟩
  intro s τ t
  apply (hnorm s τ t).trans_lt
  apply max_lt_iff.mpr
  have ht : (l t:ℝ)≤d := by
    change d*(t:ℝ)≤d
    nlinarith [t.property.2]
  exact ⟨hsmall τ (l t) ht,max_lt (hsmall 0 (l t) ht) (hsmall 1 (l t) ht)⟩
end CurveComplex.HyperellipticModel
