import CurveComplexGenusTwo.Hyperbolic.ActualThetaBasis.ActualPuncturedCylinderDoublePlaneProof
import CurveComplexGenusTwo.Hyperbolic.ActualThetaBasis.ActualCylinderThetaExactLoopTransportProof
import CurveComplexGenusTwo.Hyperbolic.ActualHaasBoundary.ActualThetaRectangleLiteralSmallCircleConjugacy
import CurveComplexGenusTwo.Hyperbolic.ActualHaasBoundary.HaasActualThetaMiddleRectanglePeripheralWordReviewRequest
open Set Topology ContinuousMap CategoryTheory
open CurveComplex.Hyperbolic CurveComplex.Hyperbolic.PantsTheta
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
theorem actual_same_complex_chart_literal_cylinder_peripheral_conjugacy_source (ρ : ℝ) (hρ : 0<ρ) (hρhalf : ρ<1/2)
    (ep : ActualPuncturedCylinder ≃ₜ {z : ℂ // z≠0 ∧ z≠1})
    (hep : ∀z : ActualPuncturedCylinder,(ep z).val=(Real.exp z.val.2:ℂ)*(z.val.1:ℂ)) :
    ∃a : ActualPuncturedCylinder,(ep a).val=1+(ρ:ℂ) ∧
    ∃γ : Path a a,
      (∀t : unitInterval,(ep (γ t)).val=1+(ρ:ℂ)*(Circle.exp (2*Real.pi*(t:ℝ)):ℂ)) ∧
    ∃stem : Path actualPantsBase a,
      Path.Homotopic
        ((actualPantsBoundaryLoop (-1) (by norm_num)).trans
          (actualPantsBoundaryLoop 1 (by norm_num)).symm)
        (stem.trans (γ.symm.trans stem.symm)) := by
  have hCylinder (ρ : ℝ) (hρ : 0<ρ) (hρhalf : ρ<1/2) :
      ∃polar : ActualPuncturedCylinder ≃ₜ ActualPuncturedRealPlane,
        (∀z : ActualPuncturedCylinder,(polar z).val=
          (Real.exp z.val.2*(z.val.1:ℂ).re,Real.exp z.val.2*(z.val.1:ℂ).im)) ∧
      ∃a : ActualPuncturedCylinder,(polar a).val=(1+ρ,0) ∧
      ∃γ : Path a a,
        (∀t : unitInterval,(polar (γ t)).val=
          (1+ρ*(Circle.exp (2*Real.pi*(t:ℝ)):ℂ).re,ρ*(Circle.exp (2*Real.pi*(t:ℝ)):ℂ).im)) ∧
      ∃stem : Path actualPantsBase a,
        Path.Homotopic
          ((actualPantsBoundaryLoop (-1) (by norm_num)).trans
            (actualPantsBoundaryLoop 1 (by norm_num)).symm)
          (stem.trans (γ.symm.trans stem.symm)) := by
    have hCyl (ρ : ℝ) (hρ : 0<ρ) (hρhalf : ρ<1/2)
        (polar : ActualPuncturedCylinder ≃ₜ ActualPuncturedRealPlane)
        (R : ActualPuncturedRealPlane ≃ₕ ActualSquareTheta)
        (hfix : ∀z : ActualSquareTheta,R (thetaRealEmbedding z)=z)
        (hb : (polar.toHomotopyEquiv.trans R) actualPantsBase=thetaBase)
        (hl : Path.Homotopic
          (((actualPantsBoundaryLoop (-1) (by norm_num)).map
            (polar.toHomotopyEquiv.trans R).continuous).cast hb.symm hb.symm) (thetaLoop false))
        (hu : Path.Homotopic
          (((actualPantsBoundaryLoop 1 (by norm_num)).map
            (polar.toHomotopyEquiv.trans R).continuous).cast hb.symm hb.symm) (thetaLoop true)) :
        ∃a : ActualPuncturedCylinder,(polar a).val=(1+ρ,0) ∧
        ∃γ : Path a a,
          (∀t : unitInterval,(polar (γ t)).val=
            (1+ρ*(Circle.exp (2*Real.pi*(t:ℝ)):ℂ).re,ρ*(Circle.exp (2*Real.pi*(t:ℝ)):ℂ).im)) ∧
        ∃stem : Path actualPantsBase a,
          Path.Homotopic
            ((actualPantsBoundaryLoop (-1) (by norm_num)).trans
              (actualPantsBoundaryLoop 1 (by norm_num)).symm)
            (stem.trans (γ.symm.trans stem.symm)) := by
      have hSmall (ρ : ℝ) (hρ : 0<ρ) (hρhalf : ρ<1/2)
          (R : ActualPuncturedRealPlane ≃ₕ ActualSquareTheta)
          (hfix : ∀z : ActualSquareTheta,R (thetaRealEmbedding z)=z) :
          ∃a : ActualPuncturedRealPlane, a.val=(1+ρ,0) ∧
          ∃γ : Path a a,
            (∀t : unitInterval,(γ t).val=(1+ρ*(Circle.exp (2*Real.pi*(t:ℝ)):ℂ).re,
              ρ*(Circle.exp (2*Real.pi*(t:ℝ)):ℂ).im)) ∧
          ∃S : Path thetaBase (R a),
            Path.Homotopic.Quotient.trans ⟦thetaLoop false⟧
              (Path.Homotopic.Quotient.symm ⟦thetaLoop true⟧)=
              ⟦S.trans ((γ.map R.continuous).symm.trans S.symm)⟧ := by
        obtain ⟨D,T,hD,hT,hword⟩ := actual_theta_middle_rectangle_peripheral_word
        let A := (thetaLeg false 0).trans (thetaLeg false 1)
        let meridian := (thetaLeg false 2).trans (T.symm.trans ((thetaLeg true 2).symm.trans D.symm))
        obtain ⟨_,_,a,ha,γ,stem,hγ,hstem,hgeom⟩ :=
          actual_theta_middle_rectangle_literal_small_circle_conjugacy ρ hρ hρhalf D T hD hT
        let σ : Path (thetaVertex false 2) (R a) :=
          (stem.map R.continuous).cast (hfix (thetaVertex false 2)).symm rfl
        let S := A.trans σ
        have hrect : (((meridian.map thetaRealEmbedding.continuous).map R.continuous).cast
            (hfix (thetaVertex false 2)).symm (hfix (thetaVertex false 2)).symm)=meridian := by
          apply Path.ext
          funext t
          exact hfix (meridian t)
        have hh : (⟦(meridian.map thetaRealEmbedding.continuous).map R.continuous⟧ :
            Path.Homotopic.Quotient (R (thetaRealEmbedding (thetaVertex false 2)))
              (R (thetaRealEmbedding (thetaVertex false 2))))=
            ⟦(stem.trans (γ.symm.trans stem.symm)).map R.continuous⟧ :=
          Quotient.sound (hgeom.map R.toFun)
        have hh' := congrArg (fun q : Path.Homotopic.Quotient
            (R (thetaRealEmbedding (thetaVertex false 2)))
            (R (thetaRealEmbedding (thetaVertex false 2))) =>
              q.cast (hfix (thetaVertex false 2)).symm (hfix (thetaVertex false 2)).symm) hh
        change ⟦(((meridian.map thetaRealEmbedding.continuous).map R.continuous).cast
          (hfix (thetaVertex false 2)).symm (hfix (thetaVertex false 2)).symm)⟧=_ at hh'
        rw [hrect] at hh'
        simp only [Path.Homotopic.Quotient.mk'_eq_mk,Path.Homotopic.Quotient.mk''_eq_mk] at hh'
        rw [←Path.Homotopic.Quotient.mk_cast] at hh'
        simp only [Path.map_trans,←Path.map_symm] at hh'
        change (⟦meridian⟧ : Path.Homotopic.Quotient _ _)=
          ⟦σ.trans ((γ.map R.continuous).symm.trans σ.symm)⟧ at hh'
        refine ⟨a,ha,γ,hγ,S,?_⟩
        rw [hword]
        change (⟦A.trans (meridian.trans A.symm)⟧ : Path.Homotopic.Quotient _ _)=_
        have hconj := congrArg (fun q : Path.Homotopic.Quotient
            (thetaVertex false 2) (thetaVertex false 2) =>
            (Path.Homotopic.Quotient.mk A).trans (q.trans (Path.Homotopic.Quotient.mk A.symm))) hh'
        simpa only [S,Path.trans_symm,Path.Homotopic.Quotient.mk'_eq_mk,
          Path.Homotopic.Quotient.mk''_eq_mk,Path.Homotopic.Quotient.mk_trans,
          Path.Homotopic.Quotient.mk_symm,Path.Homotopic.Quotient.trans_assoc] using hconj
      obtain ⟨b,hbval,η,hη,S,hword⟩ := hSmall ρ hρ hρhalf R hfix
      let E := polar.toHomotopyEquiv.trans R
      let a := polar.symm b
      let γ : Path a a := η.map polar.symm.continuous
      have hy : E a=R b := by change R (polar (polar.symm b))=R b;rw [polar.apply_symm_apply]
      let F := FundamentalGroupoidFunctor.equivOfHomotopyEquiv E
      letI : F.functor.Full := F.full_functor
      letI : F.functor.Faithful := F.faithful_functor
      have hsurj : Function.Surjective (fun q : Path.Homotopic.Quotient actualPantsBase a => q.map E.toFun) :=
        F.functor.map_surjective
      obtain ⟨q,hq⟩ := hsurj ((Path.Homotopic.Quotient.mk S).cast hb hy)
      induction q using Quotient.inductionOn with | h stem =>
        refine ⟨a,?_,γ,?_,stem,?_⟩
        · simpa only [a,polar.apply_symm_apply] using hbval
        · intro t
          change (polar (polar.symm (η t))).val=_
          rw [polar.apply_symm_apply]
          exact hη t
        · have hstem : ⟦(stem.map E.continuous).cast hb.symm hy.symm⟧=
              (Path.Homotopic.Quotient.mk S) := by
            have hh := congrArg (fun q : Path.Homotopic.Quotient (E actualPantsBase) (E a) =>
              q.cast hb.symm hy.symm) hq
            change (Path.Homotopic.Quotient.map (Path.Homotopic.Quotient.mk stem) E.toFun).cast hb.symm hy.symm=_
            simpa only [Path.Homotopic.Quotient.mk'_eq_mk,
              Path.Homotopic.Quotient.mk''_eq_mk,Path.Homotopic.Quotient.cast_cast,
              Path.Homotopic.Quotient.cast_rfl_rfl] using hh
          simp only [Path.Homotopic.Quotient.mk'_eq_mk,Path.Homotopic.Quotient.mk''_eq_mk] at hstem
          have hγ : (γ.map E.continuous).cast hy.symm hy.symm=η.map R.continuous := by
            apply Path.ext
            funext t
            change R (polar (polar.symm (η t)))=R (η t)
            rw [polar.apply_symm_apply]
          have hh : Path.Homotopic.Quotient.mk
              ((((actualPantsBoundaryLoop (-1) (by norm_num)).trans
                (actualPantsBoundaryLoop 1 (by norm_num)).symm).map E.continuous).cast hb.symm hb.symm)=
              Path.Homotopic.Quotient.mk
              (((stem.trans (γ.symm.trans stem.symm)).map E.continuous).cast hb.symm hb.symm) := by
            simp only [Path.map_trans,←Path.map_symm]
            rw [Path.cast_trans _ _ hb.symm hb.symm hb.symm,
              Path.cast_trans _ _ hb.symm hy.symm hb.symm,
              Path.cast_trans _ _ hy.symm hy.symm hb.symm,
              Path.cast_symm,Path.cast_symm,Path.cast_symm]
            change Path.Homotopic.Quotient.mk
              ((((actualPantsBoundaryLoop (-1) (by norm_num)).map E.continuous).cast hb.symm hb.symm).trans
                ((((actualPantsBoundaryLoop 1 (by norm_num)).map E.continuous).cast hb.symm hb.symm).symm))=
              Path.Homotopic.Quotient.mk
              (((stem.map E.continuous).cast hb.symm hy.symm).trans
                (((γ.map E.continuous).cast hy.symm hy.symm).symm.trans
                  ((stem.map E.continuous).cast hb.symm hy.symm).symm))
            simp only [Path.Homotopic.Quotient.mk_trans,Path.Homotopic.Quotient.mk_symm]
            rw [show Path.Homotopic.Quotient.mk
              (((actualPantsBoundaryLoop (-1) (by norm_num)).map E.continuous).cast hb.symm hb.symm)=
              Path.Homotopic.Quotient.mk (thetaLoop false) from Quotient.sound hl,
              show Path.Homotopic.Quotient.mk
              (((actualPantsBoundaryLoop 1 (by norm_num)).map E.continuous).cast hb.symm hb.symm)=
              Path.Homotopic.Quotient.mk (thetaLoop true) from Quotient.sound hu,hγ,hstem]
            exact hword
          apply Path.Homotopic.Quotient.exact
          have hinj : Function.Injective (fun q : Path.Homotopic.Quotient actualPantsBase actualPantsBase => q.map E.toFun) :=
            F.functor.map_injective
          apply hinj
          have hh' := congrArg (fun q : Path.Homotopic.Quotient thetaBase thetaBase => q.cast hb hb) hh
          simpa only [Path.Homotopic.Quotient.mk_cast,Path.Homotopic.Quotient.cast_cast,
            Path.Homotopic.Quotient.cast_rfl_rfl,
            Path.Homotopic.Quotient.mk_map] using hh'
    obtain ⟨polar,hpolar⟩ := actual_cylinder_real_plane_homeomorph
    obtain ⟨R,haxis,hfix⟩ := PantsTheta.actual_real_plane_theta_negative_axis_retraction
    let e : ActualPuncturedCylinder ≃ₕ PantsTheta.ActualSquareTheta := polar.toHomotopyEquiv.trans R
    have hb : e actualPantsBase=PantsTheta.thetaBase := by
      apply haxis 1 (by norm_num)
      change (polar actualPantsBase).val=(-1,0)
      rw [hpolar]
      simp [actualPantsBase]
    have hboth (outer : Bool) :
        let ε : ℝ := if outer then 1 else -1
        let hε : ε≠0 := by dsimp [ε];cases outer <;> norm_num
        Path.Homotopic
          (((actualPantsBoundaryLoop ε hε).map e.continuous).cast hb.symm hb.symm)
          (PantsTheta.thetaLoop outer) := by
      intro ε hε
      obtain ⟨hl,hh⟩ := PantsTheta.actual_horizontal_theta_transport polar hpolar R haxis hfix outer
      let S : Path PantsTheta.thetaBase PantsTheta.thetaBase :=
        ((actualPantsStem ε hε).map e.continuous).cast hb.symm hl.symm
      let L : Path PantsTheta.thetaBase PantsTheta.thetaBase :=
        ((actualPantsHorizontalLoop ε hε).map e.continuous).cast hl.symm hl.symm
      have hS : S=Path.refl PantsTheta.thetaBase := by
        apply Path.ext
        funext t
        change R (polar (actualPantsStem ε hε t))=PantsTheta.thetaBase
        apply haxis (Real.exp (ε*t.val)) (Real.exp_pos _)
        rw [hpolar]
        simp [actualPantsStem]
      have hL : L.Homotopic (PantsTheta.thetaLoop outer) := hh
      have hB : (((actualPantsBoundaryLoop ε hε).map e.continuous).cast hb.symm hb.symm)=
          S.trans (L.trans S.symm) := by
        dsimp only [actualPantsBoundaryLoop]
        rw [Path.map_trans,Path.map_trans,← Path.map_symm]
        rfl
      rw [hB,hS]
      have h1 : ((Path.refl PantsTheta.thetaBase).trans
          (L.trans (Path.refl PantsTheta.thetaBase))).Homotopic L :=
        Path.Homotopic.trans ⟨Path.Homotopy.reflTrans _⟩
          ⟨Path.Homotopy.transRefl L⟩
      exact h1.trans hL
    refine ⟨polar,hpolar,?_⟩
    exact hCyl ρ hρ hρhalf polar R hfix hb (hboth false) (hboth true)
  obtain ⟨polar,hpolar,a,ha,γ,hγ,stem,hword⟩ := hCylinder ρ hρ hρhalf
  have hcoords (z : ActualPuncturedCylinder) :
      (ep z).val.re=(polar z).val.1 ∧ (ep z).val.im=(polar z).val.2 := by
    rw [hep,hpolar]
    simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,zero_add,mul_zero,sub_zero]
    exact ⟨trivial,add_zero _⟩
  refine ⟨a,?_,γ,?_,stem,hword⟩
  · apply Complex.ext
    · have hh := (hcoords a).1
      rw [ha] at hh
      simpa using hh
    · have hh := (hcoords a).2
      rw [ha] at hh
      simpa using hh
  · intro t
    apply Complex.ext
    · have hh := (hcoords (γ t)).1
      rw [hγ t] at hh
      simpa using hh
    · have hh := (hcoords (γ t)).2
      rw [hγ t] at hh
      simpa using hh

