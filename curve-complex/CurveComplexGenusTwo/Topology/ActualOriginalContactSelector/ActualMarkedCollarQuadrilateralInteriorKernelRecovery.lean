import CurveComplexGenusTwo.Topology.ActualOriginalContactSelector.ActualMarkedCollarQuadrilateralParameterKernelRecovery
import CurveComplexGenusTwo.Topology.ActualOriginalContactSelector.ActualSharedMarkedTailClosedConeParameterKernelRecovery
namespace CurveComplex.LocalSurgery
open Set Topology
open scoped unitInterval

theorem actualMarkedCollarLowerConePointStrictRegion
    (r q x t : ℝ) (hr : 0<r) (hqr : r<q) (hq : q<1)
    (ht : 0<t) (ht₁ : t≤1) (hx : 0<x) (hxt : x<t) :
    0<x ∧ x<1 ∧ x*r<r*t ∧ r*t<1-x*(1-q) := by
  have hrt := mul_lt_mul_of_pos_right hqr ht
  have hxm := mul_lt_mul_of_pos_right hxt (sub_pos.mpr hq)
  have hlo : x*r<r*t := by simpa only [mul_comm] using mul_lt_mul_of_pos_right hxt hr
  refine ⟨hx,hxt.trans_le ht₁,hlo,?_⟩
  nlinarith only [hrt,hxm,ht₁]

theorem actualMarkedCollarStrictRegionParameterInterior
    (r q : ℝ) (hqr : r<q) (z : unitInterval × unitInterval)
    (hx₀ : 0<(actualMarkedCollarQuadrilateralParameterMap r q z).1)
    (hx₁ : (actualMarkedCollarQuadrilateralParameterMap r q z).1<1)
    (hy₀ : (actualMarkedCollarQuadrilateralParameterMap r q z).1*r<
      (actualMarkedCollarQuadrilateralParameterMap r q z).2)
    (hy₁ : (actualMarkedCollarQuadrilateralParameterMap r q z).2<
      1-(actualMarkedCollarQuadrilateralParameterMap r q z).1*(1-q)) :
    z.1∈Ioo (0 : unitInterval) 1 ∧ z.2∈Ioo (0 : unitInterval) 1 := by
  have hc := actualMarkedCollarQuadrilateralCoefficientPositive r q hqr z.1
  let a := 1-z.1.val+z.1.val*(q-r)
  change z.1.val*r<z.1.val*r+a*z.2.val at hy₀
  change z.1.val*r+a*z.2.val<1-z.1.val*(1-q) at hy₁
  have hzero : 0<a*z.2.val := by linarith only [hy₀]
  have he : 1-z.1.val*(1-q)=z.1.val*r+a := by dsimp [a];ring
  rw [he] at hy₁
  have hone : a*z.2.val<a := by linarith only [hy₁]
  have hpos : 0<z.2.val := by
    by_contra! ht
    have hn := mul_nonpos_of_nonneg_of_nonpos hc.le ht
    exact (not_lt_of_ge hn) hzero
  have hlt : z.2.val<1 := by
    by_contra! ht
    have hn : a≤a*z.2.val := by
      simpa using mul_le_mul_of_nonneg_left ht hc.le
    exact (not_lt_of_ge hn) hone
  exact ⟨⟨hx₀,hx₁⟩,⟨hpos,hlt⟩⟩

theorem actualSharedMarkedTailClosedLowerSquareParameterContactPath
    (r q : ℝ) (hr : 0<r) (hqr : r<q) (hq : q<1)
    (γ : C({t : unitInterval // t≠0},unitInterval))
    (hγ : ∀ t,0<(γ t).val ∧ (γ t).val<1) :
    ∃ P : Path ((0,0) : ℝ × ℝ) ((γ ⟨1,by simp⟩).val,r),IsEmbedding P ∧
      (∀ t : {t : unitInterval // t≠0},P t.val=(t.val.val*(γ t).val,r*t.val.val)) ∧
      (∀ t : unitInterval,(P t).2=r*t.val) ∧
      ∃ z : unitInterval × unitInterval,∃ Q : Path ((0,0) : unitInterval × unitInterval) z,
        IsEmbedding Q ∧
        (∀ t,actualMarkedCollarQuadrilateralParameterMap r q (Q t)=P t) ∧
        ∀ t : {t : unitInterval // t≠0},
          (Q t.val).1∈Ioo (0 : unitInterval) 1 ∧ (Q t.val).2∈Ioo (0 : unitInterval) 1 := by
  obtain ⟨P,hP,hPtrace,hPsecond,hPinside⟩ := actualSharedMarkedTailClosedConeParameterInterior r hr γ hγ
  let Ψ := actualMarkedCollarQuadrilateralParameterMap r q
  have hΨ : IsEmbedding Ψ := actualMarkedCollarQuadrilateralParameterMapEmbedding r q hqr
  have hPrange : range P⊆range Ψ := by
    rintro y ⟨t,rfl⟩
    rw [actualMarkedCollarQuadrilateralParameterMapRange r q hqr]
    by_cases ht : t=0
    · subst t
      rw [P.source]
      norm_num
    · have htpos : 0<t.val := lt_of_le_of_ne t.property.1
        (fun he => ht (Subtype.ext he.symm))
      obtain ⟨hx₀,hx₁,hy₀,hy₁⟩ := actualMarkedCollarLowerConePointStrictRegion
        r q (P t).1 t.val hr hqr hq htpos t.property.2
          (hPinside ⟨t,ht⟩).1 (hPinside ⟨t,ht⟩).2
      refine ⟨hx₀.le,hx₁.le,?_,?_⟩
      · rw [hPsecond t]
        exact hy₀.le
      · rw [hPsecond t]
        exact hy₁.le
  let H := hΨ.toHomeomorph
  let liftedPath : C(unitInterval,range Ψ) :=
    ⟨fun t => ⟨P t,hPrange ⟨t,rfl⟩⟩,P.continuous.subtype_mk _⟩
  let Q₀ : Path (H.symm (liftedPath 0)) (H.symm (liftedPath 1)) := {
    toFun := fun t => H.symm (liftedPath t)
    continuous_toFun := H.symm.continuous.comp liftedPath.continuous
    source' := rfl
    target' := rfl }
  have hQ₀ (t : unitInterval) : Ψ (Q₀ t)=P t :=
    congrArg Subtype.val (H.apply_symm_apply (liftedPath t))
  have hs : ((0,0) : unitInterval × unitInterval)=H.symm (liftedPath 0) := by
    apply hΨ.injective
    have hleft := (actualMarkedCollarQuadrilateralParameterBoundary r q).1
    exact (hleft 0).trans ((hQ₀ 0).trans P.source).symm
  let Q := Q₀.cast hs rfl
  have hQ (t : unitInterval) : Ψ (Q t)=P t := hQ₀ t
  have hQinj : Function.Injective Q := by
    intro t u he
    exact hP.injective ((hQ t).symm.trans ((congrArg Ψ he).trans (hQ u)))
  refine ⟨P,hP,hPtrace,hPsecond,_,Q,(Q.continuous.isClosedEmbedding hQinj).isEmbedding,hQ,?_⟩
  intro t
  have htpos : 0<t.val.val := lt_of_le_of_ne t.val.property.1
    (fun he => t.property (Subtype.ext he.symm))
  obtain ⟨hx₀,hx₁,hy₀,hy₁⟩ := actualMarkedCollarLowerConePointStrictRegion
    r q (P t.val).1 t.val.val hr hqr hq htpos t.val.property.2
      (hPinside t).1 (hPinside t).2
  apply actualMarkedCollarStrictRegionParameterInterior r q hqr (Q t.val)
  · rw [hQ]
    exact hx₀
  · rw [hQ]
    exact hx₁
  · rw [hQ,hPsecond]
    exact hy₀
  · rw [hQ,hPsecond]
    exact hy₁
end CurveComplex.LocalSurgery
