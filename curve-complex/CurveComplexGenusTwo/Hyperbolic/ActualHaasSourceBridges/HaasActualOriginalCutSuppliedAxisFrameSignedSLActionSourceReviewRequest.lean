import CurveComplexGenusTwo.Hyperbolic.OriginalG1.ActualDeckDevelopmentIsometryPROVED
import Mathlib
import CurveComplexGenusTwo.Hyperbolic.Stabilizer
import CurveComplexGenusTwo.Hyperbolic.VerticalRigidity
open Set Topology Matrix
open scoped UpperHalfPlane MatrixGroups Pointwise
open CurveComplex CurveComplex.Hyperbolic
set_option maxHeartbeats 8000000
set_option maxRecDepth 12000
theorem actual_original_cut_supplied_axis_frame_signed_sl_action_source {E G : Type} [MetricSpace E] [Group G]
    (a : MulAction G H2) (p : H2 → E) (hq : letI := a;IsQuotientCoveringMap p G)
    (hmetric : ∀z : H2,∃W : Set H2,IsOpen W ∧ z∈W ∧
      ∀y∈W,∀z∈W,dist (p y) (p z)=dist y z)
    (Q : Set E) (hQ : IsOpen Q) (x : H2) (hx : p x∈Q)
    (α : ℝ → H2) (hα : Isometry α) (T : ℝ) (δ : G)
    (hδD : letI := a;δ∈MulAction.stabilizer G (connectedComponentIn (p ⁻¹' Q) x))
    (hfront : range α⊆frontier (connectedComponentIn (p ⁻¹' Q) x))
    (hshift : (∀t : ℝ,@SMul.smul G H2 a.toSMul δ (α t)=α (t+T)) ∨
      (∀t : ℝ,@SMul.smul G H2 a.toSMul δ⁻¹ (α t)=α (t+T)))
    (e : H2 ≃ᵢ H2) (hframe : e.symm '' range α=range verticalPath) :
    ∃L : ℝ,(L=T ∨ L=-T) ∧
      let D : SL(2,ℝ) := ⟨!![Real.exp (L/2),0;0,Real.exp (-(L/2))],by simp [Matrix.det_fin_two,←Real.exp_add]⟩
      ∀z : H2,e.symm (@SMul.smul G H2 a.toSMul δ (e z))=D • z := by
  have hFrame (e g : H2 ≃ᵢ H2) (α : ℝ → H2) (hα : Isometry α)
      (T : ℝ) (hclock : ∀t : ℝ,g (α t)=α (t+T))
      (hframe : e.symm '' range α=range verticalPath)
      (C : Set H2) (hC : IsPreconnected C) (hne : C.Nonempty)
      (havoid : Disjoint C (range α)) (hpres : g '' C=C) :
      ∃L : ℝ,(L=T ∨ L=-T) ∧
        let D : SL(2,ℝ) := ⟨!![Real.exp (L/2),0;0,Real.exp (-(L/2))],by simp [Matrix.det_fin_two,←Real.exp_add]⟩
        ∀z : H2,e.symm (g (e z))=D • z := by
    have hTranslator (g : H2 ≃ᵢ H2) (L : ℝ) (hclock : ∀t : ℝ,g (verticalPath t)=verticalPath (t+L))
        (C : Set H2) (hC : IsPreconnected C) (hne : C.Nonempty)
        (havoid : Disjoint C (range verticalPath)) (hpres : g '' C=C) :
        let D : SL(2,ℝ) := ⟨!![Real.exp (L/2),0;0,Real.exp (-(L/2))],by simp [Matrix.det_fin_two,←Real.exp_add]⟩
        ∀z : H2,g z=D • z := by
      intro D
      have hRigid (g : H2 → H2) (hg : Isometry g)
          (h0 : g (verticalPath 0)=verticalPath 0)
          (h1 : g (verticalPath 1)=verticalPath 1)
          (z₀ : H2) (hz₀ : z₀.re≠0) (hfix : g z₀=z₀) : ∀z : H2,g z=z := by
        have hCoordinates (z w : H2)
            (h0 : dist (verticalPath 0) z=dist (verticalPath 0) w)
            (h1 : dist (verticalPath 1) z=dist (verticalPath 1) w) :
            z.im=w.im ∧ z.re^2=w.re^2 := by
          have hc0 := congrArg Real.cosh h0
          have hc1 := congrArg Real.cosh h1
          rw [UpperHalfPlane.cosh_dist',UpperHalfPlane.cosh_dist'] at hc0 hc1
          simp only [verticalPath,UpperHalfPlane.mk_re,UpperHalfPlane.mk_im,
            Real.exp_zero,zero_pow (by norm_num : (2:ℕ)≠0),zero_sub,neg_sq,zero_add,mul_one] at hc0 hc1
          have hz : 0<z.im := z.im_pos
          have hw : 0<w.im := w.im_pos
          have hb : 1<Real.exp (1:ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
          have he0 : w.im*(z.re^2+z.im^2+1)=z.im*(w.re^2+w.im^2+1) := by
            field_simp at hc0
            nlinarith [hc0]
          have he1 : w.im*(z.re^2+z.im^2+(Real.exp (1:ℝ))^2)=
              z.im*(w.re^2+w.im^2+(Real.exp (1:ℝ))^2) := by
            field_simp at hc1
            nlinarith [hc1]
          have him : z.im=w.im := by
            have hp : 0<(Real.exp (1:ℝ))^2-1 := by nlinarith
            have hf : ((Real.exp (1:ℝ))^2-1)*(z.im-w.im)=0 := by nlinarith [he0,he1]
            have hh := (mul_eq_zero.mp hf).resolve_left hp.ne'
            exact sub_eq_zero.mp hh
          refine ⟨him,?_⟩
          rw [him] at he0
          have hh : w.im*(z.re^2-w.re^2)=0 := by nlinarith [he0]
          exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hw.ne')
        intro z
        have hc := hCoordinates (g z) z (by simpa only [h0] using hg.dist_eq (verticalPath 0) z)
          (by simpa only [h1] using hg.dist_eq (verticalPath 1) z)
        have hd := congrArg Real.cosh (hg.dist_eq z z₀)
        rw [hfix,UpperHalfPlane.cosh_dist',UpperHalfPlane.cosh_dist'] at hd
        rw [hc.1] at hd
        have hp : z₀.re*((g z).re-z.re)=0 := by
          field_simp at hd
          nlinarith [hc.2]
        have hre : (g z).re=z.re := sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hz₀)
        exact UpperHalfPlane.ext_re_im hre hc.1
      have hCoordinates (z w : H2)
          (h0 : dist (verticalPath 0) z=dist (verticalPath 0) w)
          (h1 : dist (verticalPath 1) z=dist (verticalPath 1) w) :
          z.im=w.im ∧ z.re^2=w.re^2 := by
        have hc0 := congrArg Real.cosh h0
        have hc1 := congrArg Real.cosh h1
        rw [UpperHalfPlane.cosh_dist',UpperHalfPlane.cosh_dist'] at hc0 hc1
        simp only [verticalPath,UpperHalfPlane.mk_re,UpperHalfPlane.mk_im,
          Real.exp_zero,zero_pow (by norm_num : (2:ℕ)≠0),zero_sub,neg_sq,zero_add,mul_one] at hc0 hc1
        have hz : 0<z.im := z.im_pos
        have hw : 0<w.im := w.im_pos
        have hb : 1<Real.exp (1:ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
        have he0 : w.im*(z.re^2+z.im^2+1)=z.im*(w.re^2+w.im^2+1) := by
          field_simp at hc0
          nlinarith [hc0]
        have he1 : w.im*(z.re^2+z.im^2+(Real.exp (1:ℝ))^2)=
            z.im*(w.re^2+w.im^2+(Real.exp (1:ℝ))^2) := by
          field_simp at hc1
          nlinarith [hc1]
        have him : z.im=w.im := by
          have hp : 0<(Real.exp (1:ℝ))^2-1 := by nlinarith
          have hf : ((Real.exp (1:ℝ))^2-1)*(z.im-w.im)=0 := by nlinarith [he0,he1]
          have hh := (mul_eq_zero.mp hf).resolve_left hp.ne'
          exact sub_eq_zero.mp hh
        refine ⟨him,?_⟩
        rw [him] at he0
        have hh : w.im*(z.re^2-w.re^2)=0 := by nlinarith [he0]
        exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hw.ne')
      have hDiagonal (s : ℝ) :
          let D : SL(2,ℝ) := ⟨!![Real.exp (s/2),0;0,Real.exp (-(s/2))],by simp [Matrix.det_fin_two,←Real.exp_add]⟩
          ∀z : H2,(D • z).re=Real.exp s*z.re ∧ (D • z).im=Real.exp s*z.im := by
        intro D
        intro z
        have hc : ((D • z : H2) : ℂ)=
            (Real.exp s : ℂ)*(z:ℂ) := by
          rw [UpperHalfPlane.coe_specialLinearGroup_apply]
          simp [D,UpperHalfPlane.num,UpperHalfPlane.denom]
          rw [div_eq_mul_inv,←Complex.exp_neg]
          simp only [neg_neg]
          rw [mul_right_comm,←Complex.exp_add]
          congr 2
          ring
        constructor
        · simpa [Complex.mul_re,Complex.exp_ofReal_re,Complex.exp_ofReal_im] using congrArg Complex.re hc
        · simpa [Complex.mul_im,Complex.exp_ofReal_re,Complex.exp_ofReal_im] using congrArg Complex.im hc
      let Dm : SL(2,ℝ) := ⟨!![Real.exp (-L/2),0;0,Real.exp (-(-L/2))],by simp [Matrix.det_fin_two,←Real.exp_add]⟩
      let g' : H2 ≃ᵢ H2 := g.trans (IsometryEquiv.constSMul Dm)
      have hDm (z : H2) : (Dm • z).re=Real.exp (-L)*z.re ∧ (Dm • z).im=Real.exp (-L)*z.im :=
        hDiagonal (-L) z
      have hD (z : H2) : (D • z).re=Real.exp L*z.re ∧ (D • z).im=Real.exp L*z.im :=
        hDiagonal L z
      have hnormclock (t : ℝ) : g' (verticalPath t)=verticalPath t := by
        change Dm • g (verticalPath t)=verticalPath t
        rw [hclock]
        apply UpperHalfPlane.ext_re_im
        · rw [(hDm _).1];simp [verticalPath]
        · rw [(hDm _).2]
          simp only [verticalPath,UpperHalfPlane.mk_im]
          rw [←Real.exp_add]
          congr 1;ring
      have hnonzero (z : H2) (hz : z∈C) : z.re≠0 := by
        intro he
        have hv : z=verticalPath (Real.log z.im) := by
          apply UpperHalfPlane.ext_re_im
          · simpa [verticalPath] using he
          · simp [verticalPath,Real.exp_log z.im_pos]
        exact disjoint_left.mp havoid hz ⟨Real.log z.im,hv.symm⟩
      obtain ⟨z,hz⟩ := hne
      have hgz : g z∈C := hpres ▸ ⟨z,hz,rfl⟩
      have hcoords := hCoordinates (g' z) z (by simpa only [hnormclock] using g'.isometry.dist_eq (verticalPath 0) z)
        (by simpa only [hnormclock] using g'.isometry.dist_eq (verticalPath 1) z)
      have hre : (g' z).re=z.re := by
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hcoords.2 with he|he
        · exact he
        · exfalso
          have hz0 := hnonzero z hz
          have he' : Real.exp (-L)*(g z).re=-z.re := (hDm (g z)).1.symm.trans he
          have hscale : 0 < Real.exp (-L) := Real.exp_pos _
          rcases lt_or_gt_of_ne hz0 with hn|hp
          · have hgzpos : 0 < (g z).re := by nlinarith
            have hbetween : (0:ℝ)∈Icc z.re (g z).re := ⟨hn.le,hgzpos.le⟩
            obtain ⟨w,hw,hwr⟩ := hC.intermediate_value hz hgz UpperHalfPlane.continuous_re.continuousOn hbetween
            exact hnonzero w hw hwr
          · have hgzneg : (g z).re < 0 := by nlinarith
            have hbetween : (0:ℝ)∈Icc (g z).re z.re := ⟨hgzneg.le,hp.le⟩
            obtain ⟨w,hw,hwr⟩ := hC.intermediate_value hgz hz UpperHalfPlane.continuous_re.continuousOn hbetween
            exact hnonzero w hw hwr
      have hfix : g' z=z := UpperHalfPlane.ext_re_im hre hcoords.1
      have hgid : ∀z : H2,g' z=z := hRigid g' g'.isometry (hnormclock 0) (hnormclock 1) z (hnonzero z hz) hfix
      intro w
      have hwre : Real.exp (-L)*(g w).re=w.re :=
        (hDm (g w)).1.symm.trans (congrArg UpperHalfPlane.re (hgid w))
      have hwim : Real.exp (-L)*(g w).im=w.im :=
        (hDm (g w)).2.symm.trans (congrArg UpperHalfPlane.im (hgid w))
      have hprod : Real.exp L*Real.exp (-L)=1 := by rw [←Real.exp_add];simp
      have hr := congrArg (fun r : ℝ => Real.exp L*r) hwre
      have hi := congrArg (fun r : ℝ => Real.exp L*r) hwim
      simp only [←mul_assoc,hprod,one_mul] at hr hi
      exact UpperHalfPlane.ext_re_im (hr.trans (hD w).1.symm) (hi.trans (hD w).2.symm)
    have hPhase (α : ℝ → H2) (hα : Isometry α) (hrange : range α=range verticalPath) :
        ∃r : ℝ,(∀t : ℝ,α t=verticalPath (r+t)) ∨ (∀t : ℝ,α t=verticalPath (r-t)) := by
      have hSign (f : ℝ → ℝ) (hf : Isometry f) :
          (∀t : ℝ,f t=f 0+t) ∨ (∀t : ℝ,f t=f 0-t) := by
        let A : ℝ →ᵃⁱ[ℝ] ℝ := hf.affineIsometryOfStrictConvexSpace
        let k : ℝ := A.toAffineMap.linear 1
        have hfac (t : ℝ) : f t=t*k+f 0 := by
          have h := A.toAffineMap.map_vadd 0 t
          have hlin : A.toAffineMap.linear t=t*k := by
            have hh := A.toAffineMap.linear.map_smul t (1:ℝ)
            simpa [k,smul_eq_mul] using hh
          change f (t+0)=A.toAffineMap.linear t+f 0 at h
          simpa only [add_zero,hlin] using h
        have hk : |k|=1 := by
          have h := hf.dist_eq 1 0
          rw [hfac 1,hfac 0] at h
          simpa [Real.dist_eq] using h
        rcases abs_eq (by norm_num : (0:ℝ)≤1) |>.mp hk with he|he
        · left;intro t;rw [hfac,he];ring
        · right;intro t;rw [hfac,he];ring
      let f : ℝ → ℝ := fun t => Real.log (α t).im
      have hfac (t : ℝ) : α t=verticalPath (f t) := by
        have hm : α t∈range verticalPath := hrange ▸ mem_range_self t
        obtain ⟨s,hs⟩ := hm
        apply UpperHalfPlane.ext_re_im
        · have hh := congrArg UpperHalfPlane.re hs
          simpa [verticalPath] using hh.symm
        · simp [f,verticalPath,Real.exp_log (α t).im_pos]
      have hf : Isometry f := by
        apply isometry_iff_dist_eq.mpr
        intro s t
        rw [←verticalPath_isometry.dist_eq,←hfac,←hfac,hα.dist_eq]
      refine ⟨f 0,?_⟩
      rcases hSign f hf with hs|hs
      · left;intro t;rw [hfac,hs]
      · right;intro t;rw [hfac,hs]
    let ψ : ℝ → H2 := e.symm ∘ α
    have hψ : Isometry ψ := e.symm.isometry.comp hα
    have hψrange : range ψ=range verticalPath := by
      change range (e.symm ∘ α)=range verticalPath
      rw [range_comp,hframe]
    let g' : H2 ≃ᵢ H2 := (e.trans g).trans e.symm
    let C' := e.symm '' C
    have hC' : IsPreconnected C' := hC.image e.symm e.symm.continuous.continuousOn
    have hne' : C'.Nonempty := hne.image e.symm
    have havoid' : Disjoint C' (range verticalPath) := by
      apply disjoint_left.mpr
      rintro z ⟨w,hw,rfl⟩ hv
      have hm : e.symm w∈e.symm '' range α := hframe.symm ▸ hv
      obtain ⟨v,hv,he⟩ := hm
      have hvw : v=w := e.symm.injective he
      exact disjoint_left.mp havoid hw (hvw ▸ hv)
    have hpres' : g' '' C'=C' := by
      change g' '' (e.symm '' C)=e.symm '' C
      have hfun : (fun w : H2 => g' (e.symm w))=(fun w : H2 => e.symm (g w)) := by
        funext w
        simp [g']
      rw [image_image,hfun,←image_image,hpres]
    have hψclock (t : ℝ) : g' (ψ t)=ψ (t+T) := by
      change e.symm (g (e (e.symm (α t))))=e.symm (α (t+T))
      rw [e.apply_symm_apply,hclock]
    obtain ⟨r,hphase⟩ := hPhase ψ hψ hψrange
    rcases hphase with hp|hm
    · have hc : ∀u : ℝ,g' (verticalPath u)=verticalPath (u+T) := by
        intro u
        have hh := hψclock (u-r)
        rw [hp,hp] at hh
        convert hh using 1 <;> congr 1 <;> ring
      refine ⟨T,Or.inl rfl,?_⟩
      exact hTranslator g' T hc C' hC' hne' havoid' hpres'
    · have hc : ∀u : ℝ,g' (verticalPath u)=verticalPath (u-T) := by
        intro u
        have hh := hψclock (r-u)
        rw [hm,hm] at hh
        convert hh using 1 <;> congr 1 <;> ring
      refine ⟨-T,Or.inr rfl,?_⟩
      have hc' : ∀u : ℝ,g' (verticalPath u)=verticalPath (u+(-T)) := by simpa only [sub_eq_add_neg] using hc
      exact hTranslator g' (-T) hc' C' hC' hne' havoid' hpres'
  letI := a
  let C := connectedComponentIn (p ⁻¹' Q) x
  have hC : IsPreconnected C := isPreconnected_connectedComponentIn
  have hne : C.Nonempty := ⟨x,mem_connectedComponentIn hx⟩
  have hCopen : IsOpen C := (hQ.preimage hq.isCoveringMap.continuous).connectedComponentIn
  have havoid : Disjoint C (range α) :=
    (disjoint_frontier_iff_isOpen.mpr hCopen).symm.mono_right hfront
  have hpres : (fun z => δ • z) '' C=C := MulAction.mem_stabilizer_iff.mp hδD
  let home : H2 ≃ₜ H2 := {
    toFun := fun z => δ • z
    invFun := fun z => δ⁻¹ • z
    left_inv := inv_smul_smul δ
    right_inv := smul_inv_smul δ
    continuous_toFun := hq.continuous_const_smul δ
    continuous_invFun := hq.continuous_const_smul δ⁻¹ }
  have hiso : Isometry (fun z => δ • z) :=
    actual_deck_development_isometry p (Homeomorph.refl H2) hmetric home (fun z=>hq.map_smul δ)
  let deck : H2 ≃ᵢ H2 := { toEquiv := MulAction.toPerm δ, isometry_toFun := hiso }
  have hdeckpres : deck '' C=C := hpres
  rcases hshift with hs|hs
  · have hc : ∀t : ℝ,deck (α t)=α (t+T) := hs
    exact hFrame e deck α hα T hc hframe C hC hne havoid hdeckpres
  · have hs' (t : ℝ) : δ⁻¹ • α t=α (t+T) := hs t
    have hc : ∀t : ℝ,deck (α t)=α (t+(-T)) := by
      intro t
      have hh := congrArg (fun z => δ • z) (hs' (t-T))
      have hh' : α (t-T)=δ • α t := by simpa only [smul_inv_smul,sub_add_cancel] using hh
      change δ • α t=α (t+(-T))
      simpa only [sub_eq_add_neg] using hh'.symm
    obtain ⟨L,hL,hact⟩ := hFrame e deck α hα (-T) hc hframe C hC hne havoid hdeckpres
    refine ⟨L,?_,hact⟩
    rcases hL with hL|hL
    · exact Or.inr hL
    · exact Or.inl (by simpa only [neg_neg] using hL)

