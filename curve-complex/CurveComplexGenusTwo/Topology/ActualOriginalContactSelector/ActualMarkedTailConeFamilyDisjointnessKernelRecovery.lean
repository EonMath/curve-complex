import CurveComplexGenusTwo.Topology.ActualOriginalContactSelector.ActualSharedMarkedTailClosedConeParameterKernelRecovery
namespace CurveComplex.LocalSurgery
open Set Topology
open scoped unitInterval

theorem actualMarkedTailConePositiveFamilyTraceInjective
    {ι : Type*} (r : ℝ) (hr : r≠0)
    (γ : ι → {t : unitInterval // t≠0} → unitInterval)
    (hγ : ∀ t,Function.Injective (fun k => γ k t))
    (P : ι → unitInterval → ℝ × ℝ)
    (htrace : ∀ k (t : {t : unitInterval // t≠0}),
      P k t.val=(t.val.val*(γ k t).val,r*t.val.val)) :
    Function.Injective (fun z : ι × {t : unitInterval // t≠0} => P z.1 z.2.val) := by
  rintro ⟨k,t⟩ ⟨l,u⟩ he
  change P k t.val=P l u.val at he
  rw [htrace,htrace] at he
  have htimes : t=u := by
    apply Subtype.ext
    apply Subtype.ext
    exact mul_left_cancel₀ hr (congrArg Prod.snd he)
  subst u
  have ht : t.val.val≠0 := by
    intro he
    exact t.property (Subtype.ext he)
  have hlevels : γ k t=γ l t := by
    apply Subtype.ext
    exact mul_left_cancel₀ ht (congrArg Prod.fst he)
  exact Prod.ext (hγ t hlevels) rfl

theorem actualMarkedTailConeDifferentLevelsOnlyMeetAtMarkedTip
    {ι : Type*} (r : ℝ) (hr : r≠0)
    (γ : ι → {t : unitInterval // t≠0} → unitInterval)
    (hγ : ∀ t,Function.Injective (fun k => γ k t))
    (P : ι → unitInterval → ℝ × ℝ)
    (hzero : ∀ k,P k 0=(0,0))
    (htrace : ∀ k (t : {t : unitInterval // t≠0}),
      P k t.val=(t.val.val*(γ k t).val,r*t.val.val))
    (k l : ι) (hkl : k≠l) :
    range (P k)∩range (P l)={(0,0)} := by
  ext y
  constructor
  · rintro ⟨⟨t,rfl⟩,⟨u,hu⟩⟩
    by_cases ht : t=0
    · subst t
      exact mem_singleton_iff.mpr (hzero k)
    by_cases hu₀ : u=0
    · subst u
      exact mem_singleton_iff.mpr (hu.symm.trans (hzero l))
    have hpair := actualMarkedTailConePositiveFamilyTraceInjective r hr γ hγ P htrace
      (a₁ := (k,⟨t,ht⟩)) (a₂ := (l,⟨u,hu₀⟩)) hu.symm
    exact (hkl (congrArg Prod.fst hpair)).elim
  · intro hy
    have he : y=(0,0) := mem_singleton_iff.mp hy
    subst y
    exact ⟨⟨0,hzero k⟩,⟨0,hzero l⟩⟩
end CurveComplex.LocalSurgery
