import CurveComplexGenusTwo.Topology.ActualOriginalContactSelector.ActualMarkedCollarQuadrilateralInteriorKernelRecovery
namespace CurveComplex.LocalSurgery
open Set Topology
open scoped unitInterval

def actualMarkedCollarSquareReflection : C(unitInterval × unitInterval,unitInterval × unitInterval) :=
  ⟨fun z => (z.1,unitInterval.symm z.2),continuous_fst.prodMk
    (unitInterval.continuous_symm.comp continuous_snd)⟩

theorem actualMarkedCollarSquareReflectionInjective :
    Function.Injective actualMarkedCollarSquareReflection := by
  intro x y h
  apply Prod.ext
  · have he := congrArg Prod.fst h
    exact he
  · apply Subtype.ext
    have he := congrArg (fun z : unitInterval × unitInterval => z.2.val) h
    change 1-x.2.val=1-y.2.val at he
    linarith

theorem actualMarkedCollarQuadrilateralReflection (r q : ℝ)
    (z : unitInterval × unitInterval) :
    actualMarkedCollarQuadrilateralParameterMap r q (actualMarkedCollarSquareReflection z)=
      ((actualMarkedCollarQuadrilateralParameterMap (1-q) (1-r) z).1,
        1-(actualMarkedCollarQuadrilateralParameterMap (1-q) (1-r) z).2) := by
  apply Prod.ext
  · rfl
  · change z.1.val*r+(1-z.1.val+z.1.val*(q-r))*(1-z.2.val)=
      1-(z.1.val*(1-q)+(1-z.1.val+z.1.val*((1-r)-(1-q)))*z.2.val)
    ring

theorem actualSharedMarkedTailClosedUpperSquareParameterContactPath
    (r q : ℝ) (hr : 0<r) (hqr : r<q) (hq : q<1)
    (γ : C({t : unitInterval // t≠0},unitInterval))
    (hγ : ∀ t,0<(γ t).val ∧ (γ t).val<1) :
    ∃ z : unitInterval × unitInterval,∃ Q : Path ((0,1) : unitInterval × unitInterval) z,
      IsEmbedding Q ∧
      (∀ t : {t : unitInterval // t≠0},
        actualMarkedCollarQuadrilateralParameterMap r q (Q t.val)=
          (t.val.val*(γ t).val,1-(1-q)*t.val.val)) ∧
      ∀ t : {t : unitInterval // t≠0},
        (Q t.val).1∈Ioo (0 : unitInterval) 1 ∧ (Q t.val).2∈Ioo (0 : unitInterval) 1 := by
  obtain ⟨P,hP,hPtrace,hPsecond,z,Q,hQ,hQP,hQinside⟩ :=
    actualSharedMarkedTailClosedLowerSquareParameterContactPath (1-q) (1-r)
      (by linarith) (by linarith) (by linarith) γ hγ
  let R := actualMarkedCollarSquareReflection
  let Q₀ := Q.map R.continuous
  have hs : ((0,1) : unitInterval × unitInterval)=R (0,0) := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      norm_num [R,actualMarkedCollarSquareReflection,unitInterval.symm]
  let Q₁ := Q₀.cast hs rfl
  have hQ₁inj : Function.Injective Q₁ :=
    actualMarkedCollarSquareReflectionInjective.comp hQ.injective
  refine ⟨_,Q₁,(Q₁.continuous.isClosedEmbedding hQ₁inj).isEmbedding,?_,?_⟩
  · intro t
    change actualMarkedCollarQuadrilateralParameterMap r q (R (Q t.val))=_
    rw [actualMarkedCollarQuadrilateralReflection,hQP,hPtrace]
  · intro t
    obtain ⟨hx,hy⟩ := hQinside t
    refine ⟨hx,?_,?_⟩
    · change 0<1-(Q t.val).2.val
      exact sub_pos.mpr hy.2
    · change 1-(Q t.val).2.val<1
      have hp : 0<(Q t.val).2.val := hy.1
      linarith only [hp]
end CurveComplex.LocalSurgery
