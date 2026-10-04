import CurveComplexGenusTwo.Octagon.VertexChartGlueWave11

namespace CurveComplex.Octagon
set_option backward.isDefEq.respectTransparency false

theorem vertexModelPlane_range :
    Set.range vertexModelPlane = Metric.closedBall (0 : ℂ) (1 / 4) := by
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (sectorUnfoldPoint_norm p.1 p.2.1.1 p.2.1.2).trans_le p.2.2
  · intro hz
    have hρle : ‖z‖ ≤ 1 / 4 := by simpa [Metric.mem_closedBall] using hz
    by_cases hz0 : z = 0
    · subst z
      let r : unitInterval := 0
      let t : unitInterval := ⟨1/2, by constructor <;> norm_num⟩
      have hp : (r,t) ∈ quarterParams := by
        simp [quarterParams, sectorLocalRadius, sectorLocalComplex, r, t]
      refine ⟨⟨0, ⟨(r,t), hp⟩⟩, ?_⟩
      simp [vertexModelPlane, sectorUnfoldPoint, sectorLocalRadius, sectorLocalComplex, r, t]
    have hρpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hcircle : Circle.exp '' Set.Icc (0 : ℝ) (2 * Real.pi) = Set.univ := by
      simpa using (Circle.periodic_exp.image_Icc Real.two_pi_pos (0 : ℝ)).trans
        Circle.exp_surjective.range_eq
    have hmem : Circle.exp (Complex.arg z) ∈ Circle.exp '' Set.Icc (0 : ℝ) (2 * Real.pi) := by
      rw [hcircle]
      trivial
    obtain ⟨θ, hθ, heθ⟩ := hmem
    let v : ℝ := 4 * θ / Real.pi
    have hv0 : 0 ≤ v := div_nonneg (mul_nonneg (by norm_num) hθ.1) Real.pi_pos.le
    have hv8 : v ≤ 8 := by
      apply (div_le_iff₀ Real.pi_pos).2
      nlinarith [hθ.2]
    have hindex : ∃ k : Fin 8, (k.val : ℝ) ≤ v ∧ v ≤ (k.val : ℝ) + 1 := by
      by_cases hvlt : v < 8
      · refine ⟨⟨Nat.floor v, (Nat.floor_lt hv0).2 hvlt⟩, Nat.floor_le hv0, ?_⟩
        exact le_of_lt (by simpa using Nat.lt_succ_floor v)
      · refine ⟨7, ?_, ?_⟩ <;> norm_num <;> linarith
    obtain ⟨k, hklo, hkhi⟩ := hindex
    let α : ℝ := Real.pi * ((k.val : ℝ) + 1 - v)
    have hα0 : 0 ≤ α := mul_nonneg Real.pi_pos.le (by linarith)
    have hαpi : α ≤ Real.pi := by dsimp [α]; nlinarith [Real.pi_pos]
    have hs0 : 0 ≤ Real.sin α := Real.sin_nonneg_of_nonneg_of_le_pi hα0 hαpi
    let r : unitInterval := ⟨‖z‖ * Real.sin α, by
      constructor
      · exact mul_nonneg hρpos.le hs0
      · have := mul_le_mul_of_nonneg_left (Real.sin_le_one α) hρpos.le
        linarith⟩
    let t : unitInterval := ⟨1 / 2 + ‖z‖ * Real.cos α, by
      have hlow := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos α) hρpos.le
      have hhigh := mul_le_mul_of_nonneg_left (Real.cos_le_one α) hρpos.le
      constructor <;> linarith⟩
    have hlocal : sectorLocalComplex r t = ‖z‖ • (Circle.exp α : ℂ) := by
      rw [sectorLocalComplex, Circle.coe_exp, Complex.exp_mul_I]
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_eq_mul]
      dsimp [r,t]
      push_cast
      ring
    have hrad : sectorLocalRadius r t = ‖z‖ := by
      rw [sectorLocalRadius, hlocal, norm_smul, Circle.norm_coe, mul_one,
        Real.norm_eq_abs, abs_of_nonneg hρpos.le]
    have hang : sectorLocalAngle r t = α := by
      rw [sectorLocalAngle, hlocal]
      change Complex.arg ((‖z‖ : ℂ) * (Circle.exp α : ℂ)) = α
      exact (Complex.arg_real_mul (Circle.exp α : ℂ) hρpos).trans
        (Circle.arg_exp (by linarith [Real.pi_pos]) hαpi)
    have hp : (r,t) ∈ quarterParams := by
      change sectorLocalRadius r t ≤ 1 / 4
      rw [hrad]
      exact hρle
    refine ⟨⟨k, ⟨(r,t), hp⟩⟩, ?_⟩
    change sectorUnfoldPoint k r t = z
    rw [sectorUnfoldPoint, hrad]
    have hangle : sectorUnfoldAngle k r t = θ := by
      rw [sectorUnfoldAngle, hang]
      dsimp [α,v]
      field_simp
      ring
    rw [hangle, heθ, Circle.coe_exp,
      RCLike.real_smul_eq_coe_smul (K := ℂ), smul_eq_mul]
    exact Complex.norm_mul_exp_arg_mul_I z

end CurveComplex.Octagon
