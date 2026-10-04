import CurveComplexGenusTwo.Hyperbolic.CompactPolygonGeometry
import CurveComplexGenusTwo.Hyperbolic.Stabilizer

namespace CurveComplex.Hyperbolic
open scoped MatrixGroups

noncomputable def realTranslationIsometry (t : ℝ) : H2 ≃ᵢ H2 where
  toFun := fun z => t +ᵥ z
  invFun := fun z => -t +ᵥ z
  left_inv := by intro z; simp [vadd_vadd]
  right_inv := by intro z; simp [vadd_vadd]
  isometry_toFun := UpperHalfPlane.isometry_real_vadd t

noncomputable def circleStraightener (c r : ℝ) : H2 ≃ᵢ H2 :=
  ((realTranslationIsometry (-(c + r))).trans
    (IsometryEquiv.constSMul
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) ModularGroup.S))).trans
    (realTranslationIsometry (-(1 / (2 * r))))

theorem circleStraightener_coe (c r : ℝ) (z : H2) :
    (circleStraightener c r z : ℂ) =
      -((z : ℂ) - (c + r : ℝ))⁻¹ - (1 / (2 * r) : ℝ) := by
  simp only [circleStraightener, IsometryEquiv.trans_apply]
  change (-(1 / (2 * r)) : ℝ) +
    ((ModularGroup.S • ((-(c + r) : ℝ) +ᵥ z) : H2) : ℂ) = _
  rw [UpperHalfPlane.modular_S_smul]
  simp only [UpperHalfPlane.coe_vadd]
  have hv : ((-(c + r) : ℝ) : ℂ) + z = (z : ℂ) - (c + r : ℝ) := by
    push_cast
    ring
  rw [hv]
  simp only [Complex.ofReal_neg]
  ring_nf
  rw [show -(z : ℂ) + (r + c : ℝ) = -((z : ℂ) - (r + c : ℝ)) by ring,
    inv_neg]
  ring

theorem circleStraightener_re_eq_zero (c r : ℝ) (hr : 0 < r) (z : H2)
    (hz : (z.re - c) ^ 2 + z.im ^ 2 = r ^ 2) :
    (circleStraightener c r z).re = 0 := by
  change (circleStraightener c r z : ℂ).re = 0
  rw [circleStraightener_coe]
  simp only [Complex.sub_re, Complex.neg_re, Complex.inv_re,
    Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero,
    Complex.normSq_apply]
  have hden : (z.re - (c + r)) ^ 2 + z.im ^ 2 ≠ 0 := by
    nlinarith [z.im_pos, sq_nonneg (z.re - (c + r))]
  change -((z.re - (c + r)) /
      ((z.re - (c + r)) * (z.re - (c + r)) + z.im * z.im)) - 1 / (2 * r) = 0
  have hden' : (z.re - (c + r)) * (z.re - (c + r)) + z.im * z.im ≠ 0 := by
    simpa only [pow_two] using hden
  field_simp [hden', hr.ne']
  nlinarith [hz]

theorem exists_pair_vertical_isometry (a b : H2) :
    ∃ e : H2 ≃ᵢ H2, (e a).re = 0 ∧ (e b).re = 0 := by
  by_cases hab : a.re = b.re
  · refine ⟨realTranslationIsometry (-a.re), ?_, ?_⟩
    · change (-a.re +ᵥ a).re = 0
      simp only [UpperHalfPlane.vadd_re]
      ring
    · change (-a.re +ᵥ b).re = 0
      simp only [UpperHalfPlane.vadd_re]
      linarith
  · let c := semicircleCentre a b
    let r := Real.sqrt ((a.re - c) ^ 2 + a.im ^ 2)
    have hs : 0 < (a.re - c) ^ 2 + a.im ^ 2 := by
      nlinarith [a.im_pos, sq_nonneg (a.re - c)]
    have hr : 0 < r := Real.sqrt_pos.mpr hs
    have hrsq : r ^ 2 = (a.re - c) ^ 2 + a.im ^ 2 := Real.sq_sqrt hs.le
    have hcircle : (b.re - c) ^ 2 + b.im ^ 2 = r ^ 2 := by
      rw [hrsq]
      dsimp [c, semicircleCentre]
      change (b.re - (Complex.normSq (b : ℂ) - Complex.normSq (a : ℂ)) /
          (2 * (b.re - a.re))) ^ 2 + b.im ^ 2 =
        (a.re - (Complex.normSq (b : ℂ) - Complex.normSq (a : ℂ)) /
          (2 * (b.re - a.re))) ^ 2 + a.im ^ 2
      have hdiff : b.re - a.re ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
      simp only [Complex.normSq_apply, UpperHalfPlane.re, UpperHalfPlane.im] at *
      field_simp [hdiff]
      ring
    exact ⟨circleStraightener c r,
      circleStraightener_re_eq_zero c r hr a hrsq.symm,
      circleStraightener_re_eq_zero c r hr b hcircle⟩

theorem real_metric_segment_iff {a b t : ℝ} :
    dist a t + dist t b = dist a b ↔ t ∈ Set.uIcc a b := by
  rw [dist_add_dist_eq_iff]
  rcases le_total a b with hab | hba
  · rw [Set.uIcc_of_le hab, Set.mem_Icc, wbtw_iff_of_le hab]
  · rw [wbtw_comm, Set.uIcc_of_ge hba, Set.mem_Icc, wbtw_iff_of_le hba]

theorem metric_segment_iff_in_vertical_interval (e : H2 ≃ᵢ H2)
    (a b z : H2) (ha : (e a).re = 0) (hb : (e b).re = 0) :
    dist a z + dist z b = dist a b ↔
      (e z).re = 0 ∧
        Real.log (e z).im ∈ Set.uIcc (Real.log (e a).im) (Real.log (e b).im) := by
  rw [← e.dist_eq a z, ← e.dist_eq z b, ← e.dist_eq a b]
  constructor
  · intro hz
    have hre : (e z).re = 0 := (metric_segment_on_vertical (ha.trans hb.symm) hz).trans ha
    refine ⟨hre, ?_⟩
    rw [UpperHalfPlane.dist_of_re_eq (ha.trans hre.symm),
      UpperHalfPlane.dist_of_re_eq (hre.trans hb.symm),
      UpperHalfPlane.dist_of_re_eq (ha.trans hb.symm)] at hz
    exact real_metric_segment_iff.mp hz
  · rintro ⟨hre, ht⟩
    rw [UpperHalfPlane.dist_of_re_eq (ha.trans hre.symm),
      UpperHalfPlane.dist_of_re_eq (hre.trans hb.symm),
      UpperHalfPlane.dist_of_re_eq (ha.trans hb.symm)]
    exact real_metric_segment_iff.mpr ht

theorem metric_segment_has_parametrization (a b : H2) (hab : a ≠ b) :
    ∃ f : ℝ → H2, Continuous f ∧
      Set.InjOn f (Set.Icc 0 1) ∧ f 0 = a ∧ f 1 = b ∧
      f '' Set.Icc 0 1 = {z | dist a z + dist z b = dist a b} := by
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
  refine ⟨f, ?_, ?_, hf0, hf1, ?_⟩
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

theorem Hexagon.edge_has_parametrization (P : Hexagon) (i : Fin 6) :
    ∃ f : ℝ → H2, Continuous f ∧
      Set.InjOn f (Set.Icc 0 1) ∧
      f 0 = P.vertex i ∧ f 1 = P.vertex (i + 1) ∧
      f '' Set.Icc 0 1 = P.edge i := by
  apply metric_segment_has_parametrization
  intro heq
  have hi := P.injective heq
  fin_cases i <;> norm_num at hi

end CurveComplex.Hyperbolic
