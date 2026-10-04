import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSharedHorizontalGridEdgeRedraw
namespace CurveComplex.HyperellipticModel
open Set Topology
theorem actual_max_square_radial_quotient : ∃ q : C(unitInterval × {z : ℝ × ℝ // ‖z‖ = 1}, {z : ℝ × ℝ // ‖z‖ ≤ 1}),
    Function.Surjective q ∧
    (∀ a b, q a = q b → a = b ∨ a.1 = 1 ∧ b.1 = 1) ∧
    (∀ a : unitInterval × {z : ℝ × ℝ // ‖z‖ = 1}, (q a : ℝ × ℝ) = (1-a.1.val) • (a.2 : ℝ × ℝ)) := by
  let q : C(unitInterval × {z : ℝ × ℝ // ‖z‖ = 1}, {z : ℝ × ℝ // ‖z‖ ≤ 1}) :=
    ⟨fun a => ⟨(1 - (a.1 : ℝ)) • (a.2 : ℝ × ℝ), by
      rw [norm_smul, a.2.property, mul_one, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr a.1.property.2)]
      linarith [a.1.property.1]⟩,
      by fun_prop⟩
  have hnorm (a : unitInterval × {z : ℝ × ℝ // ‖z‖ = 1}) : ‖(q a : ℝ × ℝ)‖ = 1 - (a.1 : ℝ) := by
    change ‖(1 - (a.1 : ℝ)) • (a.2 : ℝ × ℝ)‖ = _
    rw [norm_smul, a.2.property, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr a.1.property.2)]
  refine ⟨q, ?_, ?_, ?_⟩
  · intro z
    by_cases hz : (z : ℝ × ℝ) = 0
    · refine ⟨(1, ⟨(1,0), by simp⟩), ?_⟩
      apply Subtype.ext
      simp [q, hz]
    · have hn : ‖(z : ℝ × ℝ)‖ ≠ 0 := norm_ne_zero_iff.mpr hz
      let u : {z : ℝ × ℝ // ‖z‖ = 1} := ⟨‖(z : ℝ × ℝ)‖⁻¹ • (z : ℝ × ℝ), by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
        exact inv_mul_cancel₀ hn⟩
      refine ⟨(⟨1 - ‖(z : ℝ × ℝ)‖, by constructor <;> linarith [z.property, norm_nonneg (z : ℝ × ℝ)]⟩, u), ?_⟩
      apply Subtype.ext
      change (1 - (1 - ‖(z : ℝ × ℝ)‖)) • (‖(z : ℝ × ℝ)‖⁻¹ • (z : ℝ × ℝ)) = (z : ℝ × ℝ)
      rw [sub_sub_cancel, smul_smul, mul_inv_cancel₀ hn, one_smul]
  · intro a b hab
    have ht : a.1 = b.1 := by
      apply Subtype.ext
      have h := congrArg (fun z : {z : ℝ × ℝ // ‖z‖ ≤ 1} => ‖(z : ℝ × ℝ)‖) hab
      rw [hnorm, hnorm] at h
      linarith
    by_cases ha : a.1 = 1
    · exact Or.inr ⟨ha, ht.symm.trans ha⟩
    · left
      apply Prod.ext ht
      apply Subtype.ext
      have h := congrArg (fun z : {z : ℝ × ℝ // ‖z‖ ≤ 1} => (z : ℝ × ℝ)) hab
      change (1 - (a.1 : ℝ)) • (a.2 : ℝ × ℝ) = (1 - (b.1 : ℝ)) • (b.2 : ℝ × ℝ) at h
      rw [← ht] at h
      have hn : 1 - (a.1 : ℝ) ≠ 0 := by
        intro he
        apply ha
        apply Subtype.ext
        change (a.1 : ℝ) = 1
        linarith
      exact (smul_right_injective _ hn) h
  · intro a
    rfl
end CurveComplex.HyperellipticModel
