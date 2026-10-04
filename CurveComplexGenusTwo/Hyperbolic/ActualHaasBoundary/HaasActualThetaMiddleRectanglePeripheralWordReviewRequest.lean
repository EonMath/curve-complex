import CurveComplexGenusTwo.Hyperbolic.ActualThetaBasis.ActualSquareThetaCover
open Set Topology
namespace CurveComplex.Hyperbolic.PantsTheta
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 6000000
theorem actual_theta_middle_rectangle_peripheral_word :
    ∃D : Path (thetaVertex false 2) (thetaVertex true 2),
    ∃T : Path (thetaVertex true 3) (thetaVertex false 3),
      (∀t : unitInterval,(D t).val=((t:ℝ),-1)) ∧
      (∀t : unitInterval,(T t).val=(1-(t:ℝ),1)) ∧
      let A := (thetaLeg false 0).trans (thetaLeg false 1)
      let meridian := (thetaLeg false 2).trans
        (T.symm.trans ((thetaLeg true 2).symm.trans D.symm))
      Path.Homotopic.Quotient.trans ⟦thetaLoop false⟧
        (Path.Homotopic.Quotient.symm ⟦thetaLoop true⟧) =
        ⟦A.trans (meridian.trans A.symm)⟧ := by
  have hEdges :
      ∃D : Path (thetaVertex false 2) (thetaVertex true 2),
      ∃T : Path (thetaVertex true 3) (thetaVertex false 3),
        (∀t : unitInterval,(D t).val=((t:ℝ),-1)) ∧
        (∀t : unitInterval,(T t).val=(1-(t:ℝ),1)) ∧
        Path.Homotopic ((thetaLeg false 1).trans D) (thetaLeg true 1) ∧
        Path.Homotopic (T.trans (thetaLeg false 3)) (thetaLeg true 3) := by
    have hSplit {X : Type} [TopologicalSpace X] {x y z : X}
        (R : Path x z) (m : unitInterval) (hm : R m=y) :
        Path.Homotopic
          (((R.subpath 0 m).cast R.source.symm hm.symm).trans
            ((R.subpath m 1).cast hm.symm R.target.symm)) R := by
      have h := Path.Homotopic.subpath_trans_subpath R 0 m 1
      rw [Path.subpath_zero_one] at h
      exact h
    let m : unitInterval := ⟨1/2,by norm_num⟩
    have hmD : thetaLeg true 1 m=thetaVertex false 2 := by
      apply Subtype.ext;norm_num [thetaLeg,thetaVertex,m]
    have hmT : thetaLeg true 3 m=thetaVertex false 3 := by
      apply Subtype.ext;norm_num [thetaLeg,thetaVertex,m]
    let D : Path (thetaVertex false 2) (thetaVertex true 2) :=
      ((thetaLeg true 1).subpath m 1).cast hmD.symm (thetaLeg true 1).target.symm
    let T : Path (thetaVertex true 3) (thetaVertex false 3) :=
      ((thetaLeg true 3).subpath 0 m).cast (thetaLeg true 3).source.symm hmT.symm
    have hD (t : unitInterval) : (D t).val=((t:ℝ),-1) := by
      dsimp [D,Path.cast,Path.subpath,thetaLeg,thetaVertex,m,Set.Icc.convexComb]
      apply Prod.ext <;> dsimp <;> norm_num <;> ring
    have hT (t : unitInterval) : (T t).val=(1-(t:ℝ),1) := by
      dsimp [T,Path.cast,Path.subpath,thetaLeg,thetaVertex,m,Set.Icc.convexComb]
      apply Prod.ext <;> dsimp <;> norm_num <;> ring
    refine ⟨D,T,hD,hT,?_,?_⟩
    · have hfirst : ((thetaLeg true 1).subpath 0 m).cast
          (thetaLeg true 1).source.symm hmD.symm=thetaLeg false 1 := by
        apply Path.ext;funext t;apply Subtype.ext
        dsimp [Path.cast,Path.subpath,thetaLeg,thetaVertex,m,Set.Icc.convexComb]
        apply Prod.ext <;> dsimp <;> norm_num <;> ring
      have hs := hSplit (thetaLeg true 1) m hmD
      rw [hfirst] at hs
      exact hs
    · have hlast : ((thetaLeg true 3).subpath m 1).cast
          hmT.symm (thetaLeg true 3).target.symm=thetaLeg false 3 := by
        apply Path.ext;funext t;apply Subtype.ext
        dsimp [Path.cast,Path.subpath,thetaLeg,thetaVertex,m,Set.Icc.convexComb]
        apply Prod.ext <;> dsimp <;> norm_num <;> ring
      have hs := hSplit (thetaLeg true 3) m hmT
      rw [hlast] at hs
      exact hs
  have hFive (o : Bool) :
      (⟦thetaLoop o⟧ : Path.Homotopic.Quotient thetaBase thetaBase)=
        Path.Homotopic.Quotient.trans ⟦thetaLeg o 0⟧
          (Path.Homotopic.Quotient.trans ⟦thetaLeg o 1⟧
            (Path.Homotopic.Quotient.trans ⟦thetaLeg o 2⟧
              (Path.Homotopic.Quotient.trans ⟦thetaLeg o 3⟧ ⟦thetaLeg o 4⟧))) := by
    cases o <;>
      simp only [thetaLoop,Path.concat_succ,Path.concat_zero,Function.comp_apply]
    all_goals
      change Path.Homotopic.Quotient.mk
        ((((((Path.refl thetaBase).trans (thetaLeg _ 0)).trans (thetaLeg _ 1)).trans
          (thetaLeg _ 2)).trans (thetaLeg _ 3)).trans (thetaLeg _ 4)) = _
      simp only [Path.Homotopic.Quotient.mk_trans,Path.Homotopic.Quotient.mk_refl,
        Path.Homotopic.Quotient.refl_trans,Path.Homotopic.Quotient.trans_assoc]
      rfl
  have hCancel {X : Type} [TopologicalSpace X] {b l u r s : X}
      (A : Path.Homotopic.Quotient b l) (B : Path.Homotopic.Quotient u b)
      (L : Path.Homotopic.Quotient l u) (D : Path.Homotopic.Quotient l r)
      (R : Path.Homotopic.Quotient r s) (T : Path.Homotopic.Quotient s u) :
      (A.trans (L.trans B)).trans
        (A.trans (D.trans (R.trans (T.trans B)))).symm =
        A.trans ((L.trans (T.symm.trans (R.symm.trans D.symm))).trans A.symm) := by
    have hs {x y z : X} (p : Path.Homotopic.Quotient x y)
        (q : Path.Homotopic.Quotient y z) : (p.trans q).symm=q.symm.trans p.symm := by
      obtain ⟨p⟩ := p
      obtain ⟨q⟩ := q
      change ⟦(p.trans q).symm⟧=⟦q.symm.trans p.symm⟧
      rw [Path.trans_symm]
    simp only [hs,Path.Homotopic.Quotient.trans_assoc]
    rw [←Path.Homotopic.Quotient.trans_assoc B B.symm,
      Path.Homotopic.Quotient.trans_symm,Path.Homotopic.Quotient.refl_trans]
  obtain ⟨D,T,hD,hT,hbottom,htop⟩ := hEdges
  refine ⟨D,T,hD,hT,?_⟩
  let A := (thetaLeg false 0).trans (thetaLeg false 1)
  let B := (thetaLeg false 3).trans (thetaLeg false 4)
  have h0 : thetaLeg true 0=thetaLeg false 0 := by
    apply Path.ext;funext t;apply Subtype.ext;rfl
  have h4 : thetaLeg true 4=thetaLeg false 4 := by
    apply Path.ext;funext t;apply Subtype.ext;rfl
  have hb : Path.Homotopic.Quotient.mk (thetaLeg true 1)=
      Path.Homotopic.Quotient.trans ⟦thetaLeg false 1⟧ ⟦D⟧ :=
    (Path.Homotopic.Quotient.eq.mpr hbottom).symm
  have ht : Path.Homotopic.Quotient.mk (thetaLeg true 3)=
      Path.Homotopic.Quotient.trans ⟦T⟧ ⟦thetaLeg false 3⟧ :=
    (Path.Homotopic.Quotient.eq.mpr htop).symm
  have hlower : (⟦thetaLoop false⟧ : Path.Homotopic.Quotient _ _)=
      Path.Homotopic.Quotient.trans ⟦A⟧
        (Path.Homotopic.Quotient.trans ⟦thetaLeg false 2⟧ ⟦B⟧) := by
    rw [hFive false]
    dsimp [A,B]
    try simp only [Path.Homotopic.Quotient.mk'_eq_mk,Path.Homotopic.Quotient.mk''_eq_mk,
      Path.Homotopic.Quotient.mk_trans,Path.Homotopic.Quotient.trans_assoc]
  have hupper : (⟦thetaLoop true⟧ : Path.Homotopic.Quotient _ _)=
      Path.Homotopic.Quotient.trans ⟦A⟧
        (Path.Homotopic.Quotient.trans ⟦D⟧
          (Path.Homotopic.Quotient.trans ⟦thetaLeg true 2⟧
            (Path.Homotopic.Quotient.trans ⟦T⟧ ⟦B⟧))) := by
    rw [hFive true]
    rw [h0,h4]
    change (Path.Homotopic.Quotient.mk _).trans
      ((Path.Homotopic.Quotient.mk _).trans
        ((Path.Homotopic.Quotient.mk _).trans
          ((Path.Homotopic.Quotient.mk _).trans (Path.Homotopic.Quotient.mk _))))=_
    rw [hb,ht]
    dsimp [A,B]
    try simp only [Path.Homotopic.Quotient.mk'_eq_mk,Path.Homotopic.Quotient.mk''_eq_mk,
      Path.Homotopic.Quotient.mk_trans,Path.Homotopic.Quotient.trans_assoc]
  dsimp only
  rw [hlower,hupper]
  have hc := hCancel (Path.Homotopic.Quotient.mk A) (Path.Homotopic.Quotient.mk B)
    (Path.Homotopic.Quotient.mk (thetaLeg false 2)) (Path.Homotopic.Quotient.mk D)
    (Path.Homotopic.Quotient.mk (thetaLeg true 2)) (Path.Homotopic.Quotient.mk T)
  convert hc using 1
  all_goals
    try dsimp only [A,B]
    try simp only [Path.Homotopic.Quotient.mk'_eq_mk,Path.Homotopic.Quotient.mk''_eq_mk,
      Path.Homotopic.Quotient.mk_trans,Path.Homotopic.Quotient.mk_symm]
    try rfl
end CurveComplex.Hyperbolic.PantsTheta
