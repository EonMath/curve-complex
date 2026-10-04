import CurveComplexGenusTwo.Hyperbolic.ActualThetaBasis.ActualPuncturedCylinderDoublePlaneProof
open Set Topology
open CurveComplex.Hyperbolic
set_option maxHeartbeats 3000000
theorem actual_same_complex_chart_meridian_cut_clock_identification {E : Type} [TopologicalSpace E] (U d : Set E)
    (f : {x : U // x.val∉d} ≃ₜ ActualPuncturedCylinder)
    (ep : ActualPuncturedCylinder ≃ₜ {z : ℂ // z≠0 ∧ z≠1})
    (j : C({z : ℂ // z≠0 ∧ ‖z‖<(1/2:ℝ)},E))
    (hj : ∀z,∃hz : (z.val+1:ℂ)≠0 ∧ (z.val+1:ℂ)≠1,
      j z=(f.symm (ep.symm ⟨z.val+1,hz⟩)).val.val)
    (ρ : ℝ) (hρ : 0<ρ) (hρhalf : ρ<1/2)
    (a : ActualPuncturedCylinder) (γ : Path a a)
    (hγ : ∀t : unitInterval,(ep (γ t)).val=
      1+(ρ:ℂ)*(Circle.exp (2*Real.pi*(t:ℝ)):ℂ)) :
    ∀t : unitInterval,
      (f.symm (γ t)).val.val=
      j ⟨(ρ:ℂ)*(Circle.exp (2*Real.pi*(t:ℝ)):ℂ),by
        constructor
        · exact mul_ne_zero (by exact_mod_cast ne_of_gt hρ) (Circle.coe_ne_zero _)
        · rw [norm_mul,Complex.norm_real,Circle.norm_coe,mul_one,
            Real.norm_eq_abs,abs_of_pos hρ]
          exact hρhalf⟩ := by
  intro t
  let w : {z : ℂ // z≠0 ∧ ‖z‖<(1/2:ℝ)} :=
    ⟨(ρ:ℂ)*(Circle.exp (2*Real.pi*(t:ℝ)):ℂ),by
      constructor
      · exact mul_ne_zero (by exact_mod_cast ne_of_gt hρ) (Circle.coe_ne_zero _)
      · rw [norm_mul,Complex.norm_real,Circle.norm_coe,mul_one,
          Real.norm_eq_abs,abs_of_pos hρ]
        exact hρhalf⟩
  obtain ⟨hz,hzj⟩ := hj w
  have hc : γ t=ep.symm ⟨w.val+1,hz⟩ := by
    apply ep.injective
    rw [ep.apply_symm_apply]
    apply Subtype.ext
    rw [hγ]
    change 1+(ρ:ℂ)*(Circle.exp (2*Real.pi*(t:ℝ)):ℂ)=
      (ρ:ℂ)*(Circle.exp (2*Real.pi*(t:ℝ)):ℂ)+1
    ring
  change (f.symm (γ t)).val.val=j w
  rw [hc]
  exact hzj.symm
