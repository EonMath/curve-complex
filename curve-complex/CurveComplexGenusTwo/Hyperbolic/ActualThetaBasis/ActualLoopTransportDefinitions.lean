import CurveComplexGenusTwo.Hyperbolic.ActualThetaBasis.HaasActualPantsDefinitions
import CurveComplexGenusTwo.Hyperbolic.ActualThetaBasis.ActualSquareThetaCover
open Set Topology ContinuousMap
namespace CurveComplex.Hyperbolic.PantsTheta
abbrev ActualPuncturedRealPlane := {z : ℝ×ℝ // z≠((0:ℝ),0) ∧ z≠((1:ℝ),0)}
noncomputable def realPlaneBase : ActualPuncturedRealPlane := ⟨(-1,0),by norm_num⟩
noncomputable def thetaRealEmbedding : C(ActualSquareTheta,ActualPuncturedRealPlane) := {
  toFun z := ⟨(z.val.1+1/2,z.val.2),by
    have havoid : z.val ≠ ((-1/2:ℝ),0) ∧ z.val ≠ ((1/2:ℝ),0) := by
      constructor <;> intro h <;> have hm := z.property <;> rw [h] at hm <;> norm_num at hm
    constructor
    · intro h
      apply havoid.1
      apply Prod.ext
      · have hx := congrArg Prod.fst h;dsimp at hx ⊢;linarith
      · have hy := congrArg (fun p : ℝ×ℝ=>p.2) h;exact hy
    · intro h
      apply havoid.2
      apply Prod.ext
      · have hx := congrArg Prod.fst h;dsimp at hx ⊢;linarith
      · have hy := congrArg (fun p : ℝ×ℝ=>p.2) h;exact hy⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.fst.add continuous_const).prodMk continuous_subtype_val.snd }
noncomputable def thetaRealStem : Path realPlaneBase (thetaRealEmbedding thetaBase) where
  toFun t := ⟨(-1+t.val/2,0),by
    have ht := t.property.2
    constructor <;> intro h <;> have hx := congrArg Prod.fst h <;> dsimp at hx <;> linarith⟩
  continuous_toFun := by fun_prop
  source' := by apply Subtype.ext;simp [realPlaneBase]
  target' := by apply Subtype.ext;norm_num [thetaRealEmbedding,thetaBase]
noncomputable def thetaRealBasedLoop (outer : Bool) : Path realPlaneBase realPlaneBase :=
  thetaRealStem.trans (((thetaLoop outer).map thetaRealEmbedding.continuous).trans thetaRealStem.symm)
noncomputable def arcMark (i : Fin 6) : unitInterval :=
  ⟨(match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 5 | 4 => 7 | _ => 8)/8,
    by fin_cases i <;> norm_num⟩
end CurveComplex.Hyperbolic.PantsTheta
