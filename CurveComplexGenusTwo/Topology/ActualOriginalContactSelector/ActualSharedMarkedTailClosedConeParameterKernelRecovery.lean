import CurveComplexGenusTwo.Topology.ActualOriginalContactSelector.ActualSharedMarkedTailCompactStripContinuityKernelRecovery
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic
namespace CurveComplex.LocalSurgery
open Set Topology
open scoped unitInterval

theorem actualSharedMarkedTailClosedConeParameterContactPath
    (r : ℝ) (hr : 0<r)
    (γ : C({t : unitInterval // t≠0},unitInterval)) :
    ∃ q : Path ((0,0) : ℝ × ℝ) ((γ ⟨1,by simp⟩).val,r),
      IsEmbedding q ∧
      (∀ t : {t : unitInterval // t≠0},q t.val=
        (t.val.val*(γ t).val,r*t.val.val)) ∧
      (∀ t : unitInterval,(q t).2=r*t.val) := by
  let K : C(unitInterval × unitInterval,ℝ × ℝ) :=
    ⟨fun z => (z.2.val*z.1.val,r*z.2.val),by fun_prop⟩
  have hzero (x : unitInterval) : K (x,0)=(0,0) := by simp [K]
  obtain ⟨q,hq,_⟩ := actualCompactStripPuncturedContactPath K (0,0) hzero 0 γ univ
    (mem_univ _) (fun _ => mem_univ _)
  have hsecond (t : unitInterval) : (q t).2=r*t.val := by
    by_cases ht : t=0
    · subst t
      rw [q.source]
      simp
    · rw [hq ⟨t,ht⟩]
      rfl
  have hinj : Function.Injective q := by
    intro t u he
    have hv := congrArg Prod.snd he
    rw [hsecond t,hsecond u] at hv
    exact Subtype.ext (mul_left_cancel₀ hr.ne' hv)
  have hend : ((γ ⟨1,by simp⟩).val,r)=K (γ ⟨1,by simp⟩,1) := by
    simp [K]
  refine ⟨q.cast rfl hend,(q.continuous.isClosedEmbedding hinj).isEmbedding,?_,hsecond⟩
  intro t
  exact hq t

theorem actualSharedMarkedTailClosedConeParameterInterior
    (r : ℝ) (hr : 0<r)
    (γ : C({t : unitInterval // t≠0},unitInterval))
    (hγ : ∀ t,0<(γ t).val ∧ (γ t).val<1) :
    ∃ q : Path ((0,0) : ℝ × ℝ) ((γ ⟨1,by simp⟩).val,r),
      IsEmbedding q ∧
      (∀ t : {t : unitInterval // t≠0},q t.val=
        (t.val.val*(γ t).val,r*t.val.val)) ∧
      (∀ t : unitInterval,(q t).2=r*t.val) ∧
      ∀ t : {t : unitInterval // t≠0},0<(q t.val).1 ∧ (q t.val).1<t.val.val := by
  obtain ⟨q,hq,htrace,hsecond⟩ := actualSharedMarkedTailClosedConeParameterContactPath r hr γ
  refine ⟨q,hq,htrace,hsecond,?_⟩
  intro t
  have ht : 0<t.val.val := lt_of_le_of_ne t.val.property.1
    (fun he => t.property (Subtype.ext he.symm))
  rw [htrace t]
  exact ⟨mul_pos ht (hγ t).1,mul_lt_of_lt_one_right ht (hγ t).2⟩
end CurveComplex.LocalSurgery
