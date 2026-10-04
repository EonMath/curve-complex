import CurveComplexGenusTwo.Hyperbolic.CompactSegmentParametrization

namespace CurveComplex.Hyperbolic
theorem metric_segment_has_constant_speed_parametrization (a b : H2) (hab : a ≠ b) :
    ∃ f : ℝ → H2, Continuous f ∧
      Set.InjOn f (Set.Icc 0 1) ∧ f 0 = a ∧ f 1 = b ∧
      f '' Set.Icc 0 1 = {z | dist a z + dist z b = dist a b} ∧
      ∀ t u : ℝ, dist (f t) (f u) = dist a b * |t - u| := by
  obtain ⟨e, ha, hb⟩ := exists_pair_vertical_isometry a b
  let α := Real.log (e a).im
  let β := Real.log (e b).im
  let f : ℝ → H2 := fun t => e.symm (verticalPath ((1 - t) * α + t * β))
  have hneq : α ≠ β := by
    intro h
    apply hab
    apply e.injective
    apply UpperHalfPlane.ext_re_im (ha.trans hb.symm)
    have h' := congrArg Real.exp h
    simpa only [α, β, Real.exp_log (e a).im_pos, Real.exp_log (e b).im_pos] using h'
  have hf0 : f 0 = a := by
    apply e.injective
    change e (e.symm (verticalPath ((1 - 0) * α + 0 * β))) = e a
    rw [e.apply_symm_apply]
    apply UpperHalfPlane.ext_re_im
    · simpa only [verticalPath, UpperHalfPlane.mk_re] using ha.symm
    · simp only [verticalPath, UpperHalfPlane.mk_im, sub_zero, one_mul, zero_mul,
        add_zero, α, Real.exp_log (e a).im_pos]
  have hf1 : f 1 = b := by
    apply e.injective
    change e (e.symm (verticalPath ((1 - 1) * α + 1 * β))) = e b
    rw [e.apply_symm_apply]
    apply UpperHalfPlane.ext_re_im
    · simpa only [verticalPath, UpperHalfPlane.mk_re] using hb.symm
    · simp only [verticalPath, UpperHalfPlane.mk_im, sub_self, one_mul, zero_mul,
        zero_add, β, Real.exp_log (e b).im_pos]
  refine ⟨f, ?_, ?_, hf0, hf1, ?_, ?_⟩
  · exact e.symm.continuous.comp (verticalPath_isometry.continuous.comp
      (((continuous_const.sub continuous_id).mul continuous_const).add
        (continuous_id.mul continuous_const)))
  · intro t ht u hu heq
    have heq' := congrArg (fun z : H2 => Real.log (e z).im) heq
    simp only [f, e.apply_symm_apply, verticalPath, UpperHalfPlane.mk_im,
      Real.log_exp] at heq'
    have hprod : (t - u) * (β - α) = 0 := by nlinarith [heq']
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right
      (sub_ne_zero.mpr (Ne.symm hneq)))
  · ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      apply (metric_segment_iff_in_vertical_interval e a b (f t) ha hb).mpr
      constructor
      · simp only [f, e.apply_symm_apply, verticalPath, UpperHalfPlane.mk_re]
      · simp only [f, e.apply_symm_apply, verticalPath, UpperHalfPlane.mk_im,
          Real.log_exp]
        rw [← segment_eq_uIcc, segment_eq_image]
        exact ⟨t, ht, by simp only [smul_eq_mul]; rfl⟩
    · intro hz
      obtain ⟨hre, hlog⟩ := (metric_segment_iff_in_vertical_interval e a b z ha hb).mp hz
      rw [← segment_eq_uIcc, segment_eq_image] at hlog
      obtain ⟨t, ht, hval⟩ := hlog
      refine ⟨t, ht, ?_⟩
      apply e.injective
      change e (e.symm (verticalPath ((1 - t) * α + t * β))) = e z
      rw [e.apply_symm_apply]
      apply UpperHalfPlane.ext_re_im
      · simpa only [verticalPath, UpperHalfPlane.mk_re] using hre.symm
      · change Real.exp ((1 - t) * α + t * β) = (e z).im
        simp only [smul_eq_mul] at hval
        rw [show (1 - t) * α + t * β = Real.log (e z).im from hval,
          Real.exp_log (e z).im_pos]

  · intro t u
    change dist (e.symm (verticalPath ((1 - t) * α + t * β)))
      (e.symm (verticalPath ((1 - u) * α + u * β))) = _
    rw [e.symm.dist_eq, verticalPath_isometry.dist_eq]
    have hd : dist a b = |β - α| := by
      rw [← e.dist_eq a b, UpperHalfPlane.dist_of_re_eq (ha.trans hb.symm), Real.dist_eq]
      exact abs_sub_comm _ _
    rw [hd, Real.dist_eq]
    have halg : (1 - t) * α + t * β - ((1 - u) * α + u * β) = (β - α) * (t - u) := by ring
    rw [halg, abs_mul]

end CurveComplex.Hyperbolic
