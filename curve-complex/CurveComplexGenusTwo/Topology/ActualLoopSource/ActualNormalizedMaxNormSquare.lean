import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualFiniteScalarNegativeIntervals
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Literal affine homeomorphism from the product max-norm closed unit ball
(the actual square) to the parameter square. -/
noncomputable def actualNormalizedMaxNormSquare : {z : ℝ × ℝ // ‖z‖≤1} ≃ₜ Interval × Interval := by
  have bounds (z : {z : ℝ × ℝ // ‖z‖≤1}) :
      (-1≤z.val.1 ∧ z.val.1≤1) ∧ (-1≤z.val.2 ∧ z.val.2≤1) := by
    simpa only [Prod.norm_def,Real.norm_eq_abs,max_le_iff,abs_le] using z.property
  exact {
    toFun := fun z =>
      (⟨(z.val.1+1)/2,by constructor <;> linarith only [(bounds z).1.1,(bounds z).1.2]⟩,
       ⟨(z.val.2+1)/2,by constructor <;> linarith only [(bounds z).2.1,(bounds z).2.2]⟩)
    invFun := fun z => ⟨(2*z.1.val-1,2*z.2.val-1),by
      simp only [Prod.norm_mk,Real.norm_eq_abs,max_le_iff,abs_le]
      constructor <;> constructor <;> linarith only [z.1.property.1,z.1.property.2,z.2.property.1,z.2.property.2]⟩
    left_inv := by intro z; apply Subtype.ext; apply Prod.ext <;> change 2*((_+1)/2)-1=_ <;> ring
    right_inv := by intro z; apply Prod.ext <;> apply Subtype.ext <;> change ((2*_-1)+1)/2=_ <;> ring
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
/-- Strict radial interior is exactly strict interior in both actual square
coordinates; this controls every later contact arc away from its endpoints. -/
theorem actual_normalized_max_norm_square_interior (z : {z : ℝ × ℝ // ‖z‖≤1}) :
    ‖z.val‖<1 ↔
      0<(actualNormalizedMaxNormSquare z).1.val ∧
      (actualNormalizedMaxNormSquare z).1.val<1 ∧
      0<(actualNormalizedMaxNormSquare z).2.val ∧
      (actualNormalizedMaxNormSquare z).2.val<1 := by
  rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,max_lt_iff,abs_lt,abs_lt]
  change (-1<z.val.1 ∧ z.val.1<1) ∧ (-1<z.val.2 ∧ z.val.2<1) ↔
    0<(z.val.1+1)/2 ∧ (z.val.1+1)/2<1 ∧
    0<(z.val.2+1)/2 ∧ (z.val.2+1)/2<1
  constructor <;> intro h
  · exact ⟨by linarith only [h.1.1],by linarith only [h.1.2],
      by linarith only [h.2.1],by linarith only [h.2.2]⟩
  · exact ⟨⟨by linarith only [h.1],by linarith only [h.2.1]⟩,
      ⟨by linarith only [h.2.2.1],by linarith only [h.2.2.2]⟩⟩
end CurveComplex.HyperellipticModel
