import CurveComplexGenusTwo.Topology.ActualOriginalContactSelector.ActualSharedMarkedTailCompactStripContinuityKernelRecovery
import Mathlib.Topology.Homotopy.Path
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible
namespace CurveComplex.LocalSurgery
open Set Topology
open scoped unitInterval
theorem actualCompactStripConstantBoundaryJointTraceContinuous
    {X P Y Z : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace P] [TopologicalSpace Y] [T1Space Y] [TopologicalSpace Z]
    (K : C(X × (P × Y),Z)) (y₀ : Y) (c : Z)
    (hboundary : ∀ x p,K (x,(p,y₀))=c) (γ : P × Y → X)
    (hγ : ContinuousOn γ {z : P × Y | z.2≠y₀}) :
    Continuous (fun z => K (γ z,z)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z.2=y₀
  · apply actualCompactStripConstantBoundaryTraceContinuousAt K z c
    intro x
    have he : z=(z.1,y₀) := Prod.ext rfl hz
    rw [he,hboundary]
  · have hop : IsOpen {z : P × Y | z.2≠y₀} :=
      isClosed_singleton.isOpen_compl.preimage continuous_snd
    exact K.continuous.continuousAt.comp
      ((hγ.continuousAt (hop.mem_nhds hz)).prodMk continuousAt_id)
theorem actualCompactStripPuncturedContactTraceHomotopicToDiagonal
    {Z : Type*} [TopologicalSpace Z]
    (K : C(unitInterval × unitInterval,Z)) (c : Z)
    (hboundary : ∀ x,K (x,0)=c)
    (γ : C({t : unitInterval // t≠0},unitInterval)) :
    ∃ f g : Path c (K (γ ⟨1,by simp⟩,1)),
      (∀ t : {t : unitInterval // t≠0},f t.val=K (γ t,t.val)) ∧
      (∀ t : unitInterval,g t=K
        (⟨t.val*(γ ⟨1,by simp⟩).val,mul_nonneg t.property.1 (γ ⟨1,by simp⟩).property.1,
          (mul_le_of_le_one_right t.property.1 (γ ⟨1,by simp⟩).property.2).trans t.property.2⟩,t)) ∧
      f.Homotopic g := by
  classical
  let γ' : unitInterval → unitInterval := fun t => if h : t=0 then 0 else γ ⟨t,h⟩
  let e : unitInterval := γ ⟨1,by simp⟩
  have hγone : γ' 1=e := by simp [γ',e]
  have hγ' : ContinuousOn γ' {(0 : unitInterval)}ᶜ := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun t : {t : unitInterval // t≠0} => γ' t.val)
    have he : (fun t : {t : unitInterval // t≠0} => γ' t.val)=γ := by
      funext t
      exact dite_eq_right t.property
    rw [he]
    exact γ.continuous
  let f : Path c (K (e,1)) :=
    { toFun := fun t => K (γ' t,t)
      continuous_toFun := actualCompactStripConstantBoundaryTraceContinuous K 0 c hboundary γ' hγ'
      source' := hboundary _
      target' := by rw [hγone] }
  let δ : C(unitInterval,unitInterval) :=
    ⟨fun t => ⟨t.val*e.val,mul_nonneg t.property.1 e.property.1,
      (mul_le_of_le_one_right t.property.1 e.property.2).trans t.property.2⟩,by fun_prop⟩
  have hδone : δ 1=e := by apply Subtype.ext;simp [δ]
  let g : Path c (K (e,1)) :=
    { toFun := fun t => K (δ t,t)
      continuous_toFun := K.continuous.comp (δ.continuous.prodMk continuous_id)
      source' := hboundary _
      target' := by rw [hδone] }
  let ρ : C(unitInterval × (unitInterval × unitInterval),unitInterval) :=
    ⟨fun z => ⟨(1-z.2.1.val)*z.1.val+z.2.1.val*(δ z.2.2).val,
      add_nonneg (mul_nonneg (sub_nonneg.mpr z.2.1.property.2) z.1.property.1)
        (mul_nonneg z.2.1.property.1 (δ z.2.2).property.1),by
      have ha := mul_le_mul_of_nonneg_left z.1.property.2 (sub_nonneg.mpr z.2.1.property.2)
      have hb := mul_le_mul_of_nonneg_left (δ z.2.2).property.2 z.2.1.property.1
      nlinarith⟩,by fun_prop⟩
  let B : C(unitInterval × (unitInterval × unitInterval),Z) :=
    K.comp ⟨fun z => (ρ z,z.2.2),by fun_prop⟩
  have hBboundary (x η : unitInterval) : B (x,(η,0))=c := hboundary _
  have hγjoint : ContinuousOn (fun z : unitInterval × unitInterval => γ' z.2)
      {z | z.2≠0} :=
    hγ'.comp continuous_snd.continuousOn (fun _ h => h)
  have hcont : Continuous (fun z : unitInterval × unitInterval => B (γ' z.2,z)) :=
    actualCompactStripConstantBoundaryJointTraceContinuous B 0 c hBboundary _ hγjoint
  have hρzero (x t : unitInterval) : ρ (x,(0,t))=x := by
    apply Subtype.ext
    simp [ρ]
  have hρone (x t : unitInterval) : ρ (x,(1,t))=δ t := by
    apply Subtype.ext
    simp [ρ]
  have hρtarget (η : unitInterval) : ρ (γ' 1,(η,1))=e := by
    apply Subtype.ext
    rw [hγone]
    change (1-η.val)*e.val+η.val*(δ 1).val=e.val
    rw [hδone]
    ring
  let H : Path.Homotopy f g :=
    { toFun := fun z => B (γ' z.2,z)
      continuous_toFun := hcont
      map_zero_left := by intro t;change K (ρ (γ' t,(0,t)),t)=_;rw [hρzero];rfl
      map_one_left := by intro t;change K (ρ (γ' t,(1,t)),t)=_;rw [hρone];rfl
      prop' := by
        intro η t ht
        rcases ht with ht | ht
        · subst t
          exact (hBboundary _ _).trans f.source.symm
        · have ht' : t=(1 : unitInterval) := ht
          subst t
          change K (ρ (γ' 1,(η,1)),1)=f 1
          rw [hρtarget,f.target] }
  refine ⟨f,g,?_,fun _ => rfl,⟨H⟩⟩
  intro t
  change K (γ' t.val,t.val)=K (γ t,t.val)
  simp only [γ',dite_eq_right t.property]
theorem actualCompactStripPuncturedContactTraceHomotopicToBoundaryRoute
    {Z : Type*} [TopologicalSpace Z]
    (K : C(unitInterval × unitInterval,Z)) (c : Z)
    (hboundary : ∀ x,K (x,0)=c)
    (γ : C({t : unitInterval // t≠0},unitInterval)) :
    ∃ f : Path c (K (γ ⟨1,by simp⟩,1)),
    ∃ v : Path c (K (0,1)),∃ w : Path (K (0,1)) (K (γ ⟨1,by simp⟩,1)),
      (∀ t : {t : unitInterval // t≠0},f t.val=K (γ t,t.val)) ∧
      (∀ t : unitInterval,v t=K (0,t)) ∧
      (∀ t : unitInterval,w t=K
        (⟨t.val*(γ ⟨1,by simp⟩).val,mul_nonneg t.property.1 (γ ⟨1,by simp⟩).property.1,
          (mul_le_of_le_one_right t.property.1 (γ ⟨1,by simp⟩).property.2).trans t.property.2⟩,1)) ∧
      f.Homotopic (v.trans w) := by
  obtain ⟨f,g,hf,hg,hhom⟩ := actualCompactStripPuncturedContactTraceHomotopicToDiagonal K c hboundary γ
  have hc : c=K (0,0) := (hboundary 0).symm
  subst c
  let e : unitInterval := γ ⟨1,by simp⟩
  let δ : C(unitInterval,unitInterval) :=
    ⟨fun t => ⟨t.val*e.val,mul_nonneg t.property.1 e.property.1,
      (mul_le_of_le_one_right t.property.1 e.property.2).trans t.property.2⟩,by fun_prop⟩
  have hδzero : δ 0=0 := by apply Subtype.ext;simp [δ]
  have hδone : δ 1=e := by apply Subtype.ext;simp [δ]
  let D : Path ((0,0) : unitInterval × unitInterval) (e,1) :=
    { toFun := fun t => (δ t,t)
      continuous_toFun := δ.continuous.prodMk continuous_id
      source' := by rw [hδzero]
      target' := by rw [hδone] }
  let P : Path ((0,0) : unitInterval × unitInterval) (0,1) :=
    { toFun := fun t => (0,t)
      continuous_toFun := continuous_const.prodMk continuous_id
      source' := rfl
      target' := rfl }
  let Q : Path ((0,1) : unitInterval × unitInterval) (e,1) :=
    { toFun := fun t => (δ t,1)
      continuous_toFun := δ.continuous.prodMk continuous_const
      source' := by rw [hδzero]
      target' := by rw [hδone] }
  let v := P.map K.continuous
  let w := Q.map K.continuous
  letI : ContractibleSpace unitInterval := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0,by norm_num⟩
  have hsquare := SimplyConnectedSpace.paths_homotopic D (P.trans Q)
  have hmap := hsquare.map K
  have hD : D.map K.continuous=g := by
    ext t
    exact (hg t).symm
  have hPQ : (P.trans Q).map K.continuous=v.trans w := by
    exact Path.map_trans P Q K.continuous
  rw [hD,hPQ] at hmap
  exact ⟨f,v,w,hf,fun _ => rfl,fun _ => rfl,hhom.trans hmap⟩
theorem actualCompactStripClosedContactTailRetainedCarrierBoundaryHomotopy
    {Z : Type*} [TopologicalSpace Z] (U : Set Z)
    (K : C(unitInterval × unitInterval,Z)) (c : Z)
    (hboundary : ∀ x,K (x,0)=c) (hcarrier : ∀ z,K z∈U)
    (γ : C({t : unitInterval // t≠0},unitInterval))
    (f : Path c (K (γ ⟨1,by simp⟩,1)))
    (htrace : ∀ t : {t : unitInterval // t≠0},f t.val=K (γ t,t.val)) :
    ∃ α : Path (⟨c,(hboundary 0) ▸ hcarrier (0,0)⟩ : U)
      ⟨K (γ ⟨1,by simp⟩,1),hcarrier _⟩,
    ∃ v : Path (⟨c,(hboundary 0) ▸ hcarrier (0,0)⟩ : U) ⟨K (0,1),hcarrier _⟩,
    ∃ w : Path (⟨K (0,1),hcarrier _⟩ : U) ⟨K (γ ⟨1,by simp⟩,1),hcarrier _⟩,
      (∀ t,(α t).val=f t) ∧
      (∀ t,(v t).val=K (0,t)) ∧
      (∀ t,(w t).val=K
        (⟨t.val*(γ ⟨1,by simp⟩).val,mul_nonneg t.property.1 (γ ⟨1,by simp⟩).property.1,
          (mul_le_of_le_one_right t.property.1 (γ ⟨1,by simp⟩).property.2).trans t.property.2⟩,1)) ∧
      α.Homotopic (v.trans w) := by
  let H : C(unitInterval × unitInterval,U) :=
    ⟨fun z => ⟨K z,hcarrier z⟩,K.continuous.subtype_mk _⟩
  let c' : U := ⟨c,(hboundary 0) ▸ hcarrier (0,0)⟩
  have hzero (x : unitInterval) : H (x,0)=c' := Subtype.ext (hboundary x)
  obtain ⟨α,v,w,hα,hv,hw,hh⟩ :=
    actualCompactStripPuncturedContactTraceHomotopicToBoundaryRoute H c' hzero γ
  refine ⟨α,v,w,?_,?_,?_,hh⟩
  · intro t
    by_cases ht : t=0
    · subst t
      exact congrArg Subtype.val α.source |>.trans f.source.symm
    · exact (congrArg Subtype.val (hα ⟨t,ht⟩)).trans (htrace ⟨t,ht⟩).symm
  · intro t
    exact congrArg Subtype.val (hv t)
  · intro t
    exact congrArg Subtype.val (hw t)
end CurveComplex.LocalSurgery
