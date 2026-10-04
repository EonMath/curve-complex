import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualLogarithmicGermContinuousRedraw
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- An actual continuous norm bound tending to zero constructs the joint
zero extension for an arbitrary parameter space, not just a single path. -/
theorem actual_product_bounded_zero_extension
    {X : Type} [TopologicalSpace X] (d : ℝ) (hd : 0<d)
    (f : C(X × Ioc (0:ℝ) d,ℂ)) (B : C(X × Icc (0:ℝ) d,ℝ))
    (hB : ∀ x, B (x,⟨0,le_rfl,hd.le⟩)=0)
    (hbound : ∀ z, ‖f z‖≤B (z.1,⟨z.2.val,z.2.property.1.le,z.2.property.2⟩)) :
    ∃ E : C(X × Icc (0:ℝ) d,ℂ),
      (∀ x, E (x,⟨0,le_rfl,hd.le⟩)=0) ∧
      ∀ z (ht : 0<z.2.val), E z=f (z.1,⟨z.2.val,ht,z.2.property.2⟩) := by
  classical
  let E : X × Icc (0:ℝ) d → ℂ := fun z =>
    if ht : 0<z.2.val then f (z.1,⟨z.2.val,ht,z.2.property.2⟩) else 0
  have hnorm (z : X × Icc (0:ℝ) d) : ‖E z‖≤B z := by
    by_cases ht : 0<z.2.val
    · dsimp only [E]
      rw [dite_eq_left ht]
      exact hbound (z.1,⟨z.2.val,ht,z.2.property.2⟩)
    · have hz : z.2=⟨0,le_rfl,hd.le⟩ :=
        Subtype.ext (le_antisymm (le_of_not_gt ht) z.2.property.1)
      have hbzero : B z=0 := by
        change B (z.1,z.2)=0
        rw [hz,hB]
      dsimp only [E]
      rw [dite_eq_right ht,hbzero]
      simp
  have hcont : Continuous E := by
    apply continuous_iff_continuousAt.mpr
    intro z
    by_cases ht : 0<z.2.val
    · let a : ℝ := z.2.val/2
      have ha : 0<a := by dsimp [a]; positivity
      have hat : a<z.2.val := by dsimp [a]; linarith
      have had : a≤d := hat.le.trans z.2.property.2
      let clamp : C(X × Icc (0:ℝ) d,X × Ioc (0:ℝ) d) :=
        ⟨fun s => (s.1,⟨max s.2.val a,ha.trans_le (le_max_right _ _),
          max_le s.2.property.2 had⟩),by fun_prop⟩
      have hopen : IsOpen {s : X × Icc (0:ℝ) d | a<s.2.val} :=
        isOpen_lt continuous_const (continuous_subtype_val.comp continuous_snd)
      have hnear : ∀ᶠ s in 𝓝 z,a<s.2.val := hopen.mem_nhds hat
      apply (f.continuous.comp clamp.continuous).continuousAt.congr_of_eventuallyEq
      filter_upwards [hnear] with s hs
      dsimp only [E]
      rw [dite_eq_left (ha.trans hs)]
      apply congrArg f
      apply Prod.ext
      · rfl
      change (⟨s.2.val,ha.trans hs,s.2.property.2⟩ : Ioc (0:ℝ) d)=
        ⟨max s.2.val a,ha.trans_le (le_max_right _ _),max_le s.2.property.2 had⟩
      apply Subtype.ext
      exact (max_eq_left hs.le).symm
    · have hz : z.2=⟨0,le_rfl,hd.le⟩ :=
        Subtype.ext (le_antisymm (le_of_not_gt ht) z.2.property.1)
      have hzero : E z=0 := dite_eq_right ht
      have hbzero : B z=0 := by
        change B (z.1,z.2)=0
        rw [hz,hB]
      have htend : Filter.Tendsto B (𝓝 z) (𝓝 (0:ℝ)) := by
        simpa only [hbzero] using (B.continuous.continuousAt (x:=z)).tendsto
      change Filter.Tendsto E (𝓝 z) (𝓝 (E z))
      rw [hzero]
      exact squeeze_zero_norm hnorm htend
  refine ⟨⟨E,hcont⟩,?_,?_⟩
  · intro x
    exact dite_eq_right (lt_irrefl (0:ℝ))
  · intro z ht
    exact dite_eq_left ht
end CurveComplex.HyperellipticModel
