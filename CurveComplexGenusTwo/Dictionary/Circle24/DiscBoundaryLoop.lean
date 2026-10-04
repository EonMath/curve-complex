import CurveComplexGenusTwo.Dictionary.OneBranchDiscBoundary
open Set Topology
namespace CurveComplex
set_option maxHeartbeats 3000000

/-- An actual once-around parameterization of the ordinary disk boundary,
with the exact endpoint collision convention of OneBranchDiscBoundary. -/
theorem unit_disc_boundary_loop_exists :
    ∃ β : C(Interval,Metric.closedBall (0:Schoenflies.Plane) 1), β 0=β 1 ∧
      (∀ s t, β s=β t → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0)) ∧
      Set.range β={z | ‖z.val‖=1} := by
  let i : ℂ ≃L[ℝ] Schoenflies.Plane :=
    Complex.equivRealProdCLM.trans ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
      (EuclideanSpace.equiv (Fin 2) ℝ).symm)
  have hinorm (z : ℂ) : ‖i z‖=‖z‖ := by
    have he0 : i z 0=z.re := rfl
    have he1 : i z 1=z.im := rfl
    have heSq : ‖i z‖^2=‖z‖^2 := by
      rw [EuclideanSpace.real_norm_sq_eq,Complex.sq_norm]
      simp [Fin.sum_univ_two,he0,he1,Complex.normSq_apply,pow_two]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp heSq
  let e : AddCircle (1:ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle one_ne_zero
  let B : C(Interval,Circle) := ⟨fun t => e (t.val:AddCircle (1:ℝ)),
    e.continuous.comp ((AddCircle.continuous_mk' 1).comp continuous_subtype_val)⟩
  let β : C(Interval,Metric.closedBall (0:Schoenflies.Plane) 1) :=
    ⟨fun t => ⟨i (B t),by simp [Metric.mem_closedBall,dist_zero_right,hinorm]⟩,
      by fun_prop⟩
  have hBclose : B 0=B 1 := by
    change e (0:AddCircle (1:ℝ))=e ((1:ℝ):AddCircle (1:ℝ))
    rw [AddCircle.coe_period]
  refine ⟨β,congrArg (fun z : Circle => (⟨i z,by simp [Metric.mem_closedBall,dist_zero_right,hinorm]⟩ :
    Metric.closedBall (0:Schoenflies.Plane) 1)) hBclose,?_,?_⟩
  · intro s t hβ
    have hB : B s=B t := Subtype.ext (i.injective (congrArg Subtype.val hβ))
    have hc : (s.val:AddCircle (1:ℝ))=(t.val:AddCircle (1:ℝ)) := e.injective hB
    by_cases hs : s=1
    · by_cases ht : t=1
      · exact Or.inl (hs.trans ht.symm)
      · have htlt : t.val<1 := lt_of_le_of_ne t.property.2
          (fun hh => ht (Subtype.ext hh))
        have ht0 : t=0 := by
          apply Subtype.ext
          have hc' : (0:AddCircle (1:ℝ))=(t.val:AddCircle (1:ℝ)) := by
            simpa only [hs,AddCircle.coe_period] using hc
          exact ((AddCircle.coe_eq_coe_iff_of_mem_Ico (a:=0) (p:=1)
            (by norm_num) (by simpa using ⟨t.property.1,htlt⟩)).mp hc').symm
        exact Or.inr (Or.inr ⟨hs,ht0⟩)
    · by_cases ht : t=1
      · have hslt : s.val<1 := lt_of_le_of_ne s.property.2
          (fun hh => hs (Subtype.ext hh))
        have hs0 : s=0 := by
          apply Subtype.ext
          have hc' : (s.val:AddCircle (1:ℝ))=(0:AddCircle (1:ℝ)) := by
            simpa only [ht,AddCircle.coe_period] using hc
          exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (a:=0) (p:=1)
            (by simpa using ⟨s.property.1,hslt⟩) (by norm_num)).mp hc'
        exact Or.inr (Or.inl ⟨hs0,ht⟩)
      · left
        have hslt : s.val<1 := lt_of_le_of_ne s.property.2 (fun hh => hs (Subtype.ext hh))
        have htlt : t.val<1 := lt_of_le_of_ne t.property.2 (fun hh => ht (Subtype.ext hh))
        apply Subtype.ext
        exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (a:=0) (p:=1)
          (by simpa using ⟨s.property.1,hslt⟩)
          (by simpa using ⟨t.property.1,htlt⟩)).mp hc
  · ext z
    constructor
    · rintro ⟨t,rfl⟩
      change ‖i (B t)‖=1
      rw [hinorm,Circle.norm_coe]
    · intro hz
      have hzC : ‖i.symm z.val‖=1 := by
        rw [← hinorm,i.apply_symm_apply]
        exact hz
      let u : Circle := ⟨i.symm z.val,by change i.symm z.val ∈ Metric.sphere (0:ℂ) 1; simpa only [Metric.mem_sphere,dist_zero_right] using hzC⟩
      obtain ⟨t,ht,hte⟩ := AddCircle.eq_coe_Ico (e.symm u)
      refine ⟨⟨t,⟨ht.1,ht.2.le⟩⟩,?_⟩
      apply Subtype.ext
      change i (e (t:AddCircle (1:ℝ)))=z.val
      rw [hte,e.apply_symm_apply]
      exact i.apply_symm_apply z.val

end CurveComplex
#print axioms CurveComplex.unit_disc_boundary_loop_exists
