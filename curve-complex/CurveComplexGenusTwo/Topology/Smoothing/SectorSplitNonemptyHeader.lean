import CurveComplexGenusTwo.Topology.Smoothing.FiniteStarSeed
open Set Metric Schoenflies

-- Splitting at an interior radial point creates two genuine cells, so the
-- convex-sector chart producer applies at the next induction stage.
theorem sector_split_interiors_nonempty (Q : Set Plane) (x e : Plane) (hx : x ∈ interior Q)
    (he : e ≠ 0) (hdet : Plane.det e x = 0) :
    (interior (Q ∩ {y | 0 ≤ Plane.det e y})).Nonempty ∧
    (interior (Q ∩ {y | Plane.det e y ≤ 0})).Nonempty := by
  have hn : 0 < ‖e‖ := norm_pos_iff.mpr he
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  let δ : ℝ := ε / (2 * ‖e‖)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hn)
  have hd : δ * ‖e‖ = ε/2 := by
    dsimp [δ]
    field_simp
  have hplus : x + δ • Plane.perp e ∈ interior Q := by
    apply hball
    rw [mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,
      Real.norm_eq_abs,abs_of_pos hδ,Plane.norm_perp,hd]
    linarith
  have hminus : x + (-δ) • Plane.perp e ∈ interior Q := by
    apply hball
    rw [mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,
      Real.norm_eq_abs,abs_neg,abs_of_pos hδ,Plane.norm_perp,hd]
    linarith
  have hcont : Continuous (fun y : Plane => Plane.det e y) := by
    unfold Plane.det
    exact (continuous_const.mul (Plane.continuous_coord 1)).sub
      (continuous_const.mul (Plane.continuous_coord 0))
  constructor
  · let U := interior Q ∩ {y | 0 < Plane.det e y}
    have hU : IsOpen U := isOpen_interior.inter (isOpen_lt continuous_const hcont)
    refine ⟨x + δ • Plane.perp e, interior_maximal ?_ hU ?_⟩
    · rintro y ⟨hyQ,hyD⟩
      exact ⟨interior_subset hyQ,show 0 ≤ Plane.det e y from (show 0 < Plane.det e y from hyD).le⟩
    · refine ⟨hplus,?_⟩
      change 0 < Plane.det e (x + δ • Plane.perp e)
      rw [Plane.det_add_right,Plane.det_smul_right,hdet,Plane.det_perp_self,zero_add]
      exact mul_pos hδ (sq_pos_of_pos hn)
  · let U := interior Q ∩ {y | Plane.det e y < 0}
    have hU : IsOpen U := isOpen_interior.inter (isOpen_lt hcont continuous_const)
    refine ⟨x + (-δ) • Plane.perp e, interior_maximal ?_ hU ?_⟩
    · rintro y ⟨hyQ,hyD⟩
      exact ⟨interior_subset hyQ,show Plane.det e y ≤ 0 from (show Plane.det e y < 0 from hyD).le⟩
    · refine ⟨hminus,?_⟩
      change Plane.det e (x + (-δ) • Plane.perp e) < 0
      rw [Plane.det_add_right,Plane.det_smul_right,hdet,Plane.det_perp_self,zero_add]
      exact mul_neg_of_neg_of_pos (neg_neg_of_pos hδ) (sq_pos_of_pos hn)

#print axioms sector_split_interiors_nonempty
