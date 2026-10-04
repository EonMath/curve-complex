import CurveComplexGenusTwo.Hyperbolic.ActualThetaBasis.ActualHorizontalThetaTransportProof
import CurveComplexGenusTwo.Hyperbolic.ActualThetaBasis.HaasActualPantsDefinitions
import CurveComplexGenusTwo.Hyperbolic.ActualThetaBasis.ActualSquareThetaCover
open Set Topology ContinuousMap
namespace CurveComplex.Hyperbolic
/-- Actual geometric deformation from the literal punctured cylinder to the
literal square theta, preserving the base and BOTH original boundary loops. -/
theorem actual_punctured_cylinder_theta_exact_loop_transport :
    ∃ e : ActualPuncturedCylinder ≃ₕ PantsTheta.ActualSquareTheta,
      ∃ hb : e actualPantsBase=PantsTheta.thetaBase,
        Path.Homotopic
          (((actualPantsBoundaryLoop (-1) (by norm_num)).map e.continuous).cast hb.symm hb.symm)
          (PantsTheta.thetaLoop false) ∧
        Path.Homotopic
          (((actualPantsBoundaryLoop 1 (by norm_num)).map e.continuous).cast hb.symm hb.symm)
          (PantsTheta.thetaLoop true) := by
  obtain ⟨polar,hpolar⟩ := actual_cylinder_real_plane_homeomorph
  obtain ⟨R,haxis,hfix⟩ := PantsTheta.actual_real_plane_theta_negative_axis_retraction
  let e : ActualPuncturedCylinder ≃ₕ PantsTheta.ActualSquareTheta := polar.toHomotopyEquiv.trans R
  have hb : e actualPantsBase=PantsTheta.thetaBase := by
    apply haxis 1 (by norm_num)
    change (polar actualPantsBase).val=(-1,0)
    rw [hpolar]
    simp [actualPantsBase]
  refine ⟨e,hb,?_⟩
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
  constructor
  · exact hboth false
  · exact hboth true
end CurveComplex.Hyperbolic
