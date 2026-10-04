import CurveComplexGenusTwo.Hyperbolic.ActualThetaBasis.ActualLoopTransportDefinitions
open Set Topology
namespace CurveComplex.Hyperbolic.PantsTheta
theorem actual_mapped_horizontal_arc_formula (e : ActualPuncturedCylinder ≃ₜ ActualPuncturedRealPlane)
    (he : ∀ z,(e z).val=(Real.exp z.val.2*(z.val.1 : ℂ).re,Real.exp z.val.2*(z.val.1 : ℂ).im)) :
    ∀ (outer : Bool) (i : Fin 5) (t : unitInterval),
      let ε : ℝ := if outer then 1 else -1
      let hε : ε≠0 := by dsimp [ε];cases outer <;> norm_num
      let φ := 2*Real.pi*((1-t.val)*(arcMark i.castSucc).val+t.val*(arcMark i.succ).val)
      ((((actualPantsHorizontalLoop ε hε).map e.continuous).subpath (arcMark i.castSucc) (arcMark i.succ)) t).val=
        (-Real.exp ε*Real.cos φ,-Real.exp ε*Real.sin φ) := by
  intro outer i t ε hε φ
  change (e (actualPantsHorizontalLoop ε hε (Set.Icc.convexComb (arcMark i.castSucc) (arcMark i.succ) t))).val=_
  rw [he]
  change (Real.exp ε*((-(1:Circle)*Circle.exp (2*Real.pi*(Set.Icc.convexComb (arcMark i.castSucc) (arcMark i.succ) t).val) : Circle):ℂ).re,
    Real.exp ε*((-(1:Circle)*Circle.exp (2*Real.pi*(Set.Icc.convexComb (arcMark i.castSucc) (arcMark i.succ) t).val) : Circle):ℂ).im)=_
  have hcircle (x : ℝ) : (Circle.exp x : ℂ)=(Real.cos x : ℂ)+(Real.sin x : ℂ)*Complex.I := by
    rw [Circle.coe_exp,Complex.exp_mul_I,← Complex.ofReal_cos,← Complex.ofReal_sin]
  simp only [Circle.coe_mul,Circle.coe_neg,Circle.coe_one,neg_one_mul,hcircle]
  apply Prod.ext <;> simp only [Complex.neg_re,Complex.neg_im,Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_mul,add_zero,zero_add]
  all_goals dsimp only [φ,Set.Icc.convexComb]; ring
end CurveComplex.Hyperbolic.PantsTheta
