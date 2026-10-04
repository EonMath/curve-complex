import Mathlib
open Set Topology
namespace CurveComplex.Hyperbolic
abbrev ActualPuncturedCylinder := {z : Circle×ℝ // z≠(1,0)}
noncomputable def actualPantsBase : ActualPuncturedCylinder :=
  ⟨(-(1 : Circle),0),by
    intro he
    have h := congrArg (fun z : Circle×ℝ => (z.1 : ℂ)) he
    norm_num at h⟩
noncomputable def actualPantsLevelPoint (ε : ℝ) (hε : ε≠0) : ActualPuncturedCylinder :=
  ⟨(-(1 : Circle),ε),by intro he;exact hε (congrArg Prod.snd he)⟩
noncomputable def actualPantsStem (ε : ℝ) (hε : ε≠0) :
    Path actualPantsBase (actualPantsLevelPoint ε hε) where
  toFun := fun t => ⟨(-(1 : Circle),ε*t.val),by
    intro he
    have h := congrArg (fun z : Circle×ℝ => (z.1 : ℂ)) he
    norm_num at h⟩
  continuous_toFun := by fun_prop
  source' := by apply Subtype.ext;simp [actualPantsBase]
  target' := by apply Subtype.ext;simp [actualPantsLevelPoint]
noncomputable def actualPantsHorizontalLoop (ε : ℝ) (hε : ε≠0) :
    Path (actualPantsLevelPoint ε hε) (actualPantsLevelPoint ε hε) where
  toFun := fun t => ⟨(-(1 : Circle)*Circle.exp (2*Real.pi*t.val),ε),by
    intro he;exact hε (congrArg Prod.snd he)⟩
  continuous_toFun := by fun_prop
  source' := by apply Subtype.ext;simp [actualPantsLevelPoint]
  target' := by apply Subtype.ext;simp [actualPantsLevelPoint,Circle.exp_two_pi]
noncomputable def actualPantsBoundaryLoop (ε : ℝ) (hε : ε≠0) :
    Path actualPantsBase actualPantsBase :=
  (actualPantsStem ε hε).trans
    ((actualPantsHorizontalLoop ε hε).trans (actualPantsStem ε hε).symm)
end CurveComplex.Hyperbolic
