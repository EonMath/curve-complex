import Schoenflies.BoundaryContinuity2
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Tactic
namespace CurveComplex.LocalSurgery
open Set Topology Schoenflies
open scoped unitInterval
noncomputable def actualUnitSquareModelPlane : C(unitInterval × unitInterval,Plane) :=
  ⟨fun z => ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
    (EuclideanSpace.equiv (Fin 2) ℝ).symm) (2*z.1.val-1,2*z.2.val-1),by fun_prop⟩

theorem actualUnitSquareModelPlaneCoordinates (z : unitInterval × unitInterval) :
    actualUnitSquareModelPlane z 0=2*z.1.val-1 ∧
    actualUnitSquareModelPlane z 1=2*z.2.val-1 := ⟨rfl,rfl⟩

theorem actualUnitSquareModelPlaneEmbedding : IsEmbedding actualUnitSquareModelPlane := by
  apply actualUnitSquareModelPlane.continuous.isClosedEmbedding _ |>.isEmbedding
  intro z w he
  have hx := congrArg (fun p : Plane => p 0) he
  have hy := congrArg (fun p : Plane => p 1) he
  change 2*z.1.val-1=2*w.1.val-1 at hx
  change 2*z.2.val-1=2*w.2.val-1 at hy
  apply Prod.ext <;> apply Subtype.ext <;> linarith

theorem actualUnitSquareModelPlaneInterior (z : unitInterval × unitInterval)
    (hz : z.1∈Ioo (0 : unitInterval) 1 ∧ z.2∈Ioo (0 : unitInterval) 1) :
    actualUnitSquareModelPlane z∈inside modelCurve := by
  rw [inside_modelCurve]
  simp only [Plane.openSquare,Plane.supDist,sub_zero] 
  change max |2*z.1.val-1| |2*z.2.val-1|<1
  rw [max_lt_iff,abs_lt,abs_lt]
  have hx₀ : 0<z.1.val := hz.1.1
  have hx₁ : z.1.val<1 := hz.1.2
  have hy₀ : 0<z.2.val := hz.2.1
  have hy₁ : z.2.val<1 := hz.2.2
  constructor <;> constructor <;> linarith

theorem actualUnitSquareModelPlaneBoundary (z : unitInterval × unitInterval)
    (hz : z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1) :
    actualUnitSquareModelPlane z∈modelCurve := by
  have hx : |2*z.1.val-1|≤1 := by rw [abs_le];constructor <;> linarith [z.1.property.1,z.1.property.2]
  have hy : |2*z.2.val-1|≤1 := by rw [abs_le];constructor <;> linarith [z.2.property.1,z.2.property.2]
  change max |2*z.1.val-1| |2*z.2.val-1|=1
  rcases hz with hz | hz | hz | hz
  · rw [hz]
    change max |2*(0 : ℝ)-1| |2*z.2.val-1|=1
    norm_num only [mul_zero,zero_sub,abs_neg,abs_one]
    exact max_eq_left hy
  · rw [hz]
    change max |2*(1 : ℝ)-1| |2*z.2.val-1|=1
    norm_num only [mul_one,show (2 : ℝ)-1=1 by norm_num,abs_one]
    exact max_eq_left hy
  · rw [hz]
    change max |2*z.1.val-1| |2*(0 : ℝ)-1|=1
    norm_num only [mul_zero,zero_sub,abs_neg,abs_one]
    exact max_eq_right hx
  · rw [hz]
    change max |2*z.1.val-1| |2*(1 : ℝ)-1|=1
    norm_num only [mul_one,show (2 : ℝ)-1=1 by norm_num,abs_one]
    exact max_eq_right hx
end CurveComplex.LocalSurgery
