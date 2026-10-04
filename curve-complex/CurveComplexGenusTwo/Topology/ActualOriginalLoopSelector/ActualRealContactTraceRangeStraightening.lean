import CurveComplexGenusTwo.Topology.ActualOriginalLoopSelector.ActualPositiveScalarTraceRange
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Constructed straightening of an actual contact trace along its selected
old-loop ray. The corner, terminal point, real axis, and positive nonvanishing
are preserved throughout; a filling is not supplied as an input. -/
theorem actual_real_contact_trace_range_straightening
    (C : C(Icc (0:ℝ) (1/2),ℂ))
    (hzero : C ⟨0,le_rfl,by norm_num⟩=0)
    (hreal : ∀ t,(C t).im=0)
    (hnz : ∀ t,0<t.val → C t≠0) :
    ∃ H : C(unitInterval × Icc (0:ℝ) (1/2),ℂ),
      (∀ t,H (0,t)=C t) ∧
      (∀ t,H (1,t)=(2*t.val) • C ⟨1/2,by norm_num,le_rfl⟩) ∧
      (∀ σ,H (σ,⟨0,le_rfl,by norm_num⟩)=0) ∧
      (∀ σ,H (σ,⟨1/2,by norm_num,le_rfl⟩)=C ⟨1/2,by norm_num,le_rfl⟩) ∧
      (∀ z,(H z).im=0) ∧ (∀ z,0<z.2.val → H z≠0) ∧
      (∀ z,H z ∈ range C) := by
  obtain ⟨f,hfzero,hfone,hfpos,hfcoord⟩ :=
    actual_real_contact_trace_branch_parameter C hzero hreal hnz
  let q : Icc (0:ℝ) (1/2) := ⟨1/2,by norm_num,le_rfl⟩
  let H : C(unitInterval × Icc (0:ℝ) (1/2),ℂ) :=
    ⟨fun z => ((1-(z.1:ℝ))*f z.2+(z.1:ℝ)*(2*z.2.val)) • C q,by fun_prop⟩
  refine ⟨H,?_,?_,?_,?_,?_,?_,?_⟩
  · intro t
    change ((1-(0:ℝ))*f t+0*(2*t.val)) • C q=C t
    simpa [q] using (hfcoord t).symm
  · intro t
    change ((1-(1:ℝ))*f t+1*(2*t.val)) • C q=(2*t.val) • C q
    simp
  · intro σ
    change ((1-(σ:ℝ))*f ⟨0,le_rfl,by norm_num⟩+(σ:ℝ)*(2*0)) • C q=0
    rw [hfzero]; simp
  · intro σ
    change ((1-(σ:ℝ))*f q+(σ:ℝ)*(2*(1/2))) • C q=C q
    rw [hfone]
    have he : (1-(σ:ℝ))*1+(σ:ℝ)*(2*(1/2))=1 := by ring
    rw [he,one_smul]
  · intro z
    simp only [H,ContinuousMap.coe_mk,Complex.smul_im,smul_eq_mul,hreal,mul_zero]
  · intro z ht
    have hc : 0<(1-(z.1:ℝ))*f z.2+(z.1:ℝ)*(2*z.2.val) := by
      by_cases hz : (z.1:ℝ)=0
      · simpa [hz] using hfpos z.2 ht
      · have hp : 0<(z.1:ℝ) := lt_of_le_of_ne z.1.property.1 (Ne.symm hz)
        exact add_pos_of_nonneg_of_pos
          (mul_nonneg (sub_nonneg.mpr z.1.property.2) (hfpos z.2 ht).le)
          (mul_pos hp (mul_pos (by norm_num) ht))
    change ((1-(z.1:ℝ))*f z.2+(z.1:ℝ)*(2*z.2.val)) • C q≠0
    exact smul_ne_zero hc.ne' (hnz q (by norm_num [q]))
  · intro z
    obtain ⟨w,hw⟩ := actual_positive_scalar_trace_interpolation_in_range
      f hfzero hfone hfpos z.1 z.2
    refine ⟨w,?_⟩
    rw [hfcoord w,hw]
    rfl
end CurveComplex.HyperellipticModel
