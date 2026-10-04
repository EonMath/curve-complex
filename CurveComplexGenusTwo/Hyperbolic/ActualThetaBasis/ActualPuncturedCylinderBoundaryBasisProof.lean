import CurveComplexGenusTwo.Hyperbolic.ActualThetaBasis.ActualFundamentalMapEquivProof
open Set Topology
namespace CurveComplex.Hyperbolic
theorem actual_punctured_cylinder_boundary_loops_fundamental_group_free_basis :
    ∃ e : FreeGroup (Fin 2) ≃* FundamentalGroup ActualPuncturedCylinder actualPantsBase,
      e (FreeGroup.of 0)=FundamentalGroup.fromPath
        ⟦actualPantsBoundaryLoop (-1) (by norm_num)⟧ ∧
      e (FreeGroup.of 1)=FundamentalGroup.fromPath
        ⟦actualPantsBoundaryLoop 1 (by norm_num)⟧ := by
  obtain ⟨E,hb,hminus,hplus⟩ := actual_punctured_cylinder_theta_exact_loop_transport
  obtain ⟨F,hF0,hF1⟩ := PantsTheta.actual_square_theta_boundary_loops_fundamental_group_free_basis
  let g : FundamentalGroup ActualPuncturedCylinder actualPantsBase ≃*
      FundamentalGroup PantsTheta.ActualSquareTheta PantsTheta.thetaBase :=
    MulEquiv.ofBijective (FundamentalGroup.mapOfEq E.toFun hb)
      (actual_fundamental_mapOfEq_bijective E actualPantsBase PantsTheta.thetaBase hb)
  refine ⟨F.trans g.symm,?_,?_⟩
  · apply g.injective
    rw [MulEquiv.trans_apply,g.apply_symm_apply,hF0]
    change (⟦PantsTheta.thetaLoop false⟧ : Path.Homotopic.Quotient _ _)=
      FundamentalGroup.mapOfEq E.toFun hb ⟦actualPantsBoundaryLoop (-1) (by norm_num)⟧
    erw [FundamentalGroup.mapOfEq_apply,← Path.Homotopic.Quotient.mk_map,
      ← Path.Homotopic.Quotient.mk_cast]
    exact Quotient.sound hminus.symm
  · apply g.injective
    rw [MulEquiv.trans_apply,g.apply_symm_apply,hF1]
    change (⟦PantsTheta.thetaLoop true⟧ : Path.Homotopic.Quotient _ _)=
      FundamentalGroup.mapOfEq E.toFun hb ⟦actualPantsBoundaryLoop 1 (by norm_num)⟧
    erw [FundamentalGroup.mapOfEq_apply,← Path.Homotopic.Quotient.mk_map,
      ← Path.Homotopic.Quotient.mk_cast]
    exact Quotient.sound hplus.symm
end CurveComplex.Hyperbolic
