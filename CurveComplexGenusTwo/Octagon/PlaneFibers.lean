import CurveComplexGenusTwo.Octagon.VertexChartGlueWave11

namespace CurveComplex.Octagon

private theorem cycle_int_same (k l : Fin 8) (m : ℤ)
    (h : (k.val : ℤ) - l.val - 8 * m = 0) : k = l := by
  apply Fin.ext
  omega

private theorem cycle_int_next (k l : Fin 8) (m : ℤ)
    (h : (k.val : ℤ) - l.val - 8 * m = 1) : k = next l := by
  fin_cases k <;> fin_cases l <;> norm_num [next] at * <;> omega

private theorem plane_angle_relation (k l : Fin 8) (r s t u : unitInterval)
    (h : sectorUnfoldPoint k r t = sectorUnfoldPoint l s u)
    (hz : sectorLocalRadius r t ≠ 0) :
    ∃ m : ℤ, sectorLocalAngle r t / Real.pi - sectorLocalAngle s u / Real.pi =
      (k.val : ℝ) - l.val - 8 * m := by
  have hρ : sectorLocalRadius r t = sectorLocalRadius s u := by
    simpa only [sectorUnfoldPoint_norm] using congrArg norm h
  have he : Circle.exp (sectorUnfoldAngle k r t) = Circle.exp (sectorUnfoldAngle l s u) := by
    apply Circle.ext
    unfold sectorUnfoldPoint at h
    rw [← hρ] at h
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ),
      RCLike.real_smul_eq_coe_smul (K := ℂ), smul_eq_mul, smul_eq_mul] at h
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hz) h
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp he
  refine ⟨m, ?_⟩
  unfold sectorUnfoldAngle at hm
  have hp := Real.pi_pos
  nlinarith

private theorem local_coords_of_polar_eq (r s t u : unitInterval)
    (hρ : sectorLocalRadius r t = sectorLocalRadius s u)
    (hθ : sectorLocalAngle r t = sectorLocalAngle s u) : r = s ∧ t = u := by
  have h1 := sectorLocal_radius_sin r t
  have h2 := sectorLocal_radius_sin s u
  have h3 := sectorLocal_radius_cos r t
  have h4 := sectorLocal_radius_cos s u
  rw [hρ, hθ] at h1 h3
  exact ⟨Subtype.ext (by linarith), Subtype.ext (by linarith)⟩

private theorem local_outgoing_of_angle_zero (p : quarterParams)
    (h : sectorLocalAngle p.1.1 p.1.2 = 0) :
    ∃ s : unitInterval, (s : ℝ) ≤ 1 / 2 ∧
      p.1.1 = 0 ∧ p.1.2 = outgoingHalf s := by
  let s : unitInterval := ⟨2 * sectorLocalRadius p.1.1 p.1.2, by
    have hp : sectorLocalRadius p.1.1 p.1.2 ≤ 1 / 4 := p.2
    have hn : 0 ≤ sectorLocalRadius p.1.1 p.1.2 := norm_nonneg _
    constructor <;> linarith⟩
  have hr := sectorLocal_radius_sin p.1.1 p.1.2
  have ht := sectorLocal_radius_cos p.1.1 p.1.2
  rw [h, Real.sin_zero, mul_zero] at hr
  rw [h, Real.cos_zero, mul_one] at ht
  refine ⟨s, ?_, Subtype.ext hr.symm, ?_⟩
  · dsimp [s]; have hp : sectorLocalRadius p.1.1 p.1.2 ≤ 1 / 4 := p.2; linarith
  · apply Subtype.ext
    dsimp [outgoingHalf, s]
    linarith

private theorem local_incoming_of_angle_pi (p : quarterParams)
    (h : sectorLocalAngle p.1.1 p.1.2 = Real.pi) :
    ∃ s : unitInterval, (s : ℝ) ≤ 1 / 2 ∧
      p.1.1 = 0 ∧ p.1.2 = incomingHalf s := by
  let s : unitInterval := ⟨2 * sectorLocalRadius p.1.1 p.1.2, by
    have hp : sectorLocalRadius p.1.1 p.1.2 ≤ 1 / 4 := p.2
    have hn : 0 ≤ sectorLocalRadius p.1.1 p.1.2 := norm_nonneg _
    constructor <;> linarith⟩
  have hr := sectorLocal_radius_sin p.1.1 p.1.2
  have ht := sectorLocal_radius_cos p.1.1 p.1.2
  rw [h, Real.sin_pi, mul_zero] at hr
  rw [h, Real.cos_pi, mul_neg_one] at ht
  refine ⟨s, ?_, Subtype.ext hr.symm, ?_⟩
  · dsimp [s]; have hp : sectorLocalRadius p.1.1 p.1.2 ≤ 1 / 4 := p.2; linarith
  · apply Subtype.ext
    dsimp [incomingHalf, s]
    linarith

private theorem plane_endpoints_source (p q : vertexModel)
    (hk : p.1 = next q.1)
    (hp : sectorLocalAngle p.2.1.1 p.2.1.2 = Real.pi)
    (hq : sectorLocalAngle q.2.1.1 q.2.1.2 = 0)
    (hρ : sectorLocalRadius p.2.1.1 p.2.1.2 =
      sectorLocalRadius q.2.1.1 q.2.1.2) :
    vertexModelSource p = vertexModelSource q := by
  obtain ⟨s, _, hr, ht⟩ := local_incoming_of_angle_pi p.2 hp
  obtain ⟨u, _, hs, hu⟩ := local_outgoing_of_angle_zero q.2 hq
  have hsu : s = u := by
    apply Subtype.ext
    rw [hr, ht, hs, hu, sectorLocalRadius_incoming, sectorLocalRadius_outgoing] at hρ
    linarith
  simp only [vertexModelSource, hr, ht, hs, hu, hsu, hk]
  exact (radialSector_seam_quotient q.1 u).symm

theorem vertexModel_plane_implies_source (p q : vertexModel)
    (h : vertexModelPlane p = vertexModelPlane q) :
    vertexModelSource p = vertexModelSource q := by
  by_cases hz : vertexModelPlane p = 0
  · exact ((vertexModel_vertex_iff_plane_zero p).mpr hz).trans
      ((vertexModel_vertex_iff_plane_zero q).mpr (h.symm.trans hz)).symm
  have hρ : sectorLocalRadius p.2.1.1 p.2.1.2 =
      sectorLocalRadius q.2.1.1 q.2.1.2 := by
    simpa only [vertexModelPlane, sectorUnfoldPoint_norm] using congrArg norm h
  have hρz : sectorLocalRadius p.2.1.1 p.2.1.2 ≠ 0 := by
    intro he
    apply hz
    simp [vertexModelPlane, sectorUnfoldPoint, he]
  obtain ⟨m, hm⟩ := plane_angle_relation p.1 q.1 _ _ _ _ h hρz
  have ha0 : 0 ≤ sectorLocalAngle p.2.1.1 p.2.1.2 / Real.pi :=
    div_nonneg (sectorLocalAngle_nonneg _ _) Real.pi_pos.le
  have ha1 : sectorLocalAngle p.2.1.1 p.2.1.2 / Real.pi ≤ 1 :=
    (div_le_one Real.pi_pos).mpr (sectorLocalAngle_le_pi _ _)
  have hb0 : 0 ≤ sectorLocalAngle q.2.1.1 q.2.1.2 / Real.pi :=
    div_nonneg (sectorLocalAngle_nonneg _ _) Real.pi_pos.le
  have hb1 : sectorLocalAngle q.2.1.1 q.2.1.2 / Real.pi ≤ 1 :=
    (div_le_one Real.pi_pos).mpr (sectorLocalAngle_le_pi _ _)
  let d : ℤ := (p.1.val : ℤ) - q.1.val - 8 * m
  have hd : (d : ℝ) = (p.1.val : ℝ) - q.1.val - 8 * m := by simp [d]
  have hd0 : -1 ≤ d := by exact_mod_cast (show (-1 : ℝ) ≤ (d : ℝ) by rw [hd]; linarith)
  have hd1 : d ≤ 1 := by exact_mod_cast (show (d : ℝ) ≤ (1 : ℝ) by rw [hd]; linarith)
  have cases : d = -1 ∨ d = 0 ∨ d = 1 := by omega
  rcases cases with he | he | he
  · have he' : (p.1.val : ℝ) - q.1.val - 8 * m = -1 := by rw [← hd, he]; norm_num
    have ha : sectorLocalAngle p.2.1.1 p.2.1.2 = 0 := by
      have hh : sectorLocalAngle p.2.1.1 p.2.1.2 / Real.pi = 0 := by linarith
      exact (div_eq_zero_iff).mp hh |>.resolve_right Real.pi_ne_zero
    have hb : sectorLocalAngle q.2.1.1 q.2.1.2 = Real.pi := by
      have hh : sectorLocalAngle q.2.1.1 q.2.1.2 / Real.pi = 1 := by linarith
      exact (div_eq_one_iff_eq Real.pi_ne_zero).mp hh
    have hk : q.1 = next p.1 := by
      apply cycle_int_next q.1 p.1 (-m)
      dsimp [d] at he
      omega
    exact (plane_endpoints_source q p hk hb ha hρ.symm).symm
  · have hk : p.1 = q.1 := cycle_int_same _ _ m he
    have he' : (p.1.val : ℝ) - q.1.val - 8 * m = 0 := by rw [← hd, he]; norm_num
    have ha : sectorLocalAngle p.2.1.1 p.2.1.2 = sectorLocalAngle q.2.1.1 q.2.1.2 := by
      apply (div_left_inj' Real.pi_ne_zero).mp
      linarith
    obtain ⟨hr, ht⟩ := local_coords_of_polar_eq _ _ _ _ hρ ha
    simp only [vertexModelSource, hk, hr, ht]
  · have he' : (p.1.val : ℝ) - q.1.val - 8 * m = 1 := by rw [← hd, he]; norm_num
    have ha : sectorLocalAngle p.2.1.1 p.2.1.2 = Real.pi := by
      have hh : sectorLocalAngle p.2.1.1 p.2.1.2 / Real.pi = 1 := by linarith
      exact (div_eq_one_iff_eq Real.pi_ne_zero).mp hh
    have hb : sectorLocalAngle q.2.1.1 q.2.1.2 = 0 := by
      have hh : sectorLocalAngle q.2.1.1 q.2.1.2 / Real.pi = 0 := by linarith
      exact (div_eq_zero_iff).mp hh |>.resolve_right Real.pi_ne_zero
    exact plane_endpoints_source p q (cycle_int_next _ _ m he) ha hb hρ

end CurveComplex.Octagon
