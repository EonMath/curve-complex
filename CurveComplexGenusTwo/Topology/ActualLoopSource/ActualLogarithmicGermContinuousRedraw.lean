import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualLogarithmicGermRedrawBound
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- The actual affine logarithmic redraw extends jointly and continuously
across the zero endpoint. No extension or convergence certificate is given. -/
theorem actual_logarithmic_germ_continuous_redraw
    (g : C(unitInterval × unitInterval,ℂ)) (hg : ∀ τ, g (τ,0)=0)
    (Λ : C(unitInterval × Ioc (0:ℝ) 1,ℂ))
    (hΛ : ∀ z, Complex.exp (Λ z)=g
      (z.1,⟨z.2.val,z.2.property.1.le,z.2.property.2⟩)) :
    ∃ D : C(unitInterval × unitInterval,ℂ),
      (∀ τ, D (τ,0)=0) ∧
      (∀ (τ t : unitInterval) (ht : 0<(t:ℝ)), D (τ,t)=Complex.exp
        ((1-(τ:ℝ)) • Λ (0,⟨t.val,ht,t.property.2⟩)+
          (τ:ℝ) • Λ (1,⟨t.val,ht,t.property.2⟩))) ∧
      (∀ t, D (0,t)=g (0,t) ∧ D (1,t)=g (1,t)) := by
  classical
  let f : C(unitInterval × Ioc (0:ℝ) 1,ℂ) :=
    ⟨fun z => Complex.exp ((1-(z.1:ℝ)) • Λ (0,z.2)+(z.1:ℝ) • Λ (1,z.2)),by fun_prop⟩
  let B : C(unitInterval × unitInterval,ℝ) :=
    ⟨fun z => max ‖g (0,z.2)‖ ‖g (1,z.2)‖,by fun_prop⟩
  let D : unitInterval × unitInterval → ℂ := fun z =>
    if ht : 0<(z.2:ℝ) then f (z.1,⟨z.2.val,ht,z.2.property.2⟩) else 0
  have hnorm (z : unitInterval × unitInterval) : ‖D z‖≤B z := by
    by_cases ht : 0<(z.2:ℝ)
    · dsimp only [D]
      rw [dite_eq_left ht]
      exact (actual_complex_log_affine_norm_le _ _ z.1).trans_eq (by rw [hΛ,hΛ]; rfl)
    · have hz : z.2=0 := Subtype.ext (le_antisymm (le_of_not_gt ht) z.2.property.1)
      simp [D,B,hz,hg]
  have hcont : Continuous D := by
    apply continuous_iff_continuousAt.mpr
    intro z
    by_cases ht : 0<(z.2:ℝ)
    · let a : ℝ := (z.2:ℝ)/2
      have ha : 0<a := by dsimp [a]; positivity
      have hat : a<(z.2:ℝ) := by dsimp [a]; linarith
      have ha1 : a≤1 := hat.le.trans z.2.property.2
      let clamp : C(unitInterval × unitInterval,unitInterval × Ioc (0:ℝ) 1) :=
        ⟨fun s => (s.1,⟨max (s.2:ℝ) a,ha.trans_le (le_max_right _ _),
          max_le s.2.property.2 ha1⟩),by fun_prop⟩
      have hopen : IsOpen {s : unitInterval × unitInterval | a<(s.2:ℝ)} :=
        isOpen_lt continuous_const (continuous_subtype_val.comp continuous_snd)
      have hnear : ∀ᶠ s in 𝓝 z, a<(s.2:ℝ) := hopen.mem_nhds hat
      apply (f.continuous.comp clamp.continuous).continuousAt.congr_of_eventuallyEq
      filter_upwards [hnear] with s hs
      dsimp only [D]
      rw [dite_eq_left (ha.trans hs)]
      apply congrArg f
      apply Prod.ext
      · rfl
      change (⟨s.2.val,ha.trans hs,s.2.property.2⟩ : Ioc (0:ℝ) 1)=
        ⟨max (s.2:ℝ) a,ha.trans_le (le_max_right _ _),max_le s.2.property.2 ha1⟩
      apply Subtype.ext
      exact (max_eq_left hs.le).symm
    · have hz : z.2=0 := Subtype.ext (le_antisymm (le_of_not_gt ht) z.2.property.1)
      have hzero : D z=0 := dite_eq_right ht
      have htend : Filter.Tendsto B (𝓝 z) (𝓝 (0:ℝ)) := by
        simpa [B,hz,hg] using (B.continuous.continuousAt (x:=z)).tendsto
      change Filter.Tendsto D (𝓝 z) (𝓝 (D z))
      rw [hzero]
      exact squeeze_zero_norm hnorm htend
  refine ⟨⟨D,hcont⟩,?_,?_,?_⟩
  · intro τ
    exact dite_eq_right (lt_irrefl (0:ℝ))
  · intro τ t ht
    exact dite_eq_left ht
  · intro t
    by_cases ht : 0<(t:ℝ)
    · constructor
      · change D (0,t)=g (0,t)
        rw [show D (0,t)=f (0,⟨t.val,ht,t.property.2⟩) from dite_eq_left ht]
        simpa [f] using hΛ (0,⟨t.val,ht,t.property.2⟩)
      · change D (1,t)=g (1,t)
        rw [show D (1,t)=f (1,⟨t.val,ht,t.property.2⟩) from dite_eq_left ht]
        simpa [f] using hΛ (1,⟨t.val,ht,t.property.2⟩)
    · have hz : t=0 := Subtype.ext (le_antisymm (le_of_not_gt ht) t.property.1)
      subst t
      simp [D,hg]
end CurveComplex.HyperellipticModel
