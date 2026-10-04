import CurveComplexGenusTwo.Hyperbolic.VerticalGeodesic
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction

namespace CurveComplex.Hyperbolic

open Matrix
open scoped MatrixGroups

private theorem verticalPath_zero_eq_I : verticalPath 0 = UpperHalfPlane.I := by
  apply UpperHalfPlane.ext_re_im <;> simp [verticalPath]

private theorem vertical_one_dist (z : H2)
    (h : dist UpperHalfPlane.I z = 1) :
    Real.exp (1 : ℝ) * (z.re ^ 2 + z.im ^ 2 + 1) =
      z.im * (1 + (Real.exp (1 : ℝ)) ^ 2) := by
  have hstd : dist (verticalPath 0) (verticalPath 1) = 1 := by
    simpa using (verticalPath_isometry.dist_eq 0 1)
  have hc := congrArg Real.cosh (h.trans (verticalPath_zero_eq_I ▸ hstd).symm)
  rw [UpperHalfPlane.cosh_dist', UpperHalfPlane.cosh_dist'] at hc
  simp only [verticalPath, UpperHalfPlane.mk_re, UpperHalfPlane.mk_im] at hc
  simp only [UpperHalfPlane.I_re, UpperHalfPlane.I_im, zero_sub,
    neg_sq, one_pow, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hc
  field_simp at hc
  nlinarith [hc]

noncomputable def stabilizerRotation (a b : ℝ) (hab : 0 < a ^ 2 + b ^ 2) :
    SL(2, ℝ) := by
  let k := Real.sqrt (a ^ 2 + b ^ 2)
  have hk : 0 < k := Real.sqrt_pos.2 hab
  have hksq : k ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt hab.le
  refine ⟨!![a / k, b / k; -b / k, a / k], ?_⟩
  simp [Matrix.det_fin_two]
  field_simp
  nlinarith [hksq]

private theorem stabilizer_denominator_ne_zero (a b : ℝ)
    (hab : 0 < a ^ 2 + b ^ 2) (w : H2) :
    (-(b : ℂ) * (w : ℂ) + a) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp [Complex.mul_im] at him
  have hb : b = 0 := by
    rcases him with hb | hw
    · exact hb
    · exact (w.im_pos.ne' hw).elim
  have ha : a ≠ 0 := by
    intro ha
    rw [ha, hb] at hab
    norm_num at hab
  exact ha (by simpa [hb] using h)

theorem stabilizerRotation_coe_smul (a b : ℝ)
    (hab : 0 < a ^ 2 + b ^ 2) (w : H2) :
    ((stabilizerRotation a b hab • w : H2) : ℂ) =
      ((a : ℂ) * w + b) / (-(b : ℂ) * w + a) := by
  have hk : 0 < Real.sqrt (a ^ 2 + b ^ 2) := Real.sqrt_pos.2 hab
  have hkC : ((Real.sqrt (a ^ 2 + b ^ 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hk.ne'
  have hden := stabilizer_denominator_ne_zero a b hab w
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [stabilizerRotation]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp [hkC, hden]

theorem stabilizerRotation_fixes_I (a b : ℝ)
    (hab : 0 < a ^ 2 + b ^ 2) :
    (stabilizerRotation a b hab • UpperHalfPlane.I : H2) = UpperHalfPlane.I := by
  apply UpperHalfPlane.coe_injective
  rw [stabilizerRotation_coe_smul]
  apply (div_eq_iff (stabilizer_denominator_ne_zero a b hab UpperHalfPlane.I)).2
  simp only [UpperHalfPlane.coe_I]
  ring_nf
  simp [Complex.I_sq]

theorem stabilizerRotation_maps_vertical_one (z : H2)
    (h : dist UpperHalfPlane.I z = 1)
    (hab : 0 < (1 - Real.exp (1 : ℝ) * z.im) ^ 2 + z.re ^ 2) :
    (stabilizerRotation (1 - Real.exp (1 : ℝ) * z.im) z.re hab •
      verticalPath 1 : H2) = z := by
  let a := 1 - Real.exp (1 : ℝ) * z.im
  let b := z.re
  have hsphere := vertical_one_dist z h
  have hEim : (Complex.exp (1 : ℂ)).im = 0 := by
    simpa using Complex.exp_ofReal_im (1 : ℝ)
  have hEre : (Complex.exp (1 : ℂ)).re = Real.exp (1 : ℝ) := by
    simpa using Complex.exp_ofReal_re (1 : ℝ)
  apply UpperHalfPlane.coe_injective
  rw [stabilizerRotation_coe_smul]
  apply (div_eq_iff (stabilizer_denominator_ne_zero a b hab (verticalPath 1))).2
  apply Complex.ext
  · simp [verticalPath, Complex.add_re, Complex.mul_re, Complex.neg_re,
      Complex.mul_im, Complex.neg_im]
    rw [hEim]
    dsimp [a, b]
    ring
  · simp [verticalPath, Complex.add_im, Complex.mul_im, Complex.neg_im,
      Complex.mul_re, Complex.neg_re]
    rw [hEre]
    dsimp [a, b]
    nlinarith [hsphere]

theorem modular_S_verticalPath (t : ℝ) :
    (ModularGroup.S • verticalPath t : H2) = verticalPath (-t) := by
  apply UpperHalfPlane.coe_injective
  rw [UpperHalfPlane.modular_S_smul]
  apply Complex.ext
  · simp [verticalPath, Complex.inv_re, Complex.normSq_apply]
  · simp [verticalPath, Complex.inv_im, Complex.normSq_apply, Real.exp_neg]
    field_simp [Real.exp_ne_zero]

theorem exists_stabilizer_map_vertical_one (z : H2)
    (h : dist UpperHalfPlane.I z = 1) :
    ∃ e : H2 ≃ᵢ H2, e UpperHalfPlane.I = UpperHalfPlane.I ∧
      e (verticalPath 1) = z := by
  let a : ℝ := 1 - Real.exp (1 : ℝ) * z.im
  let b : ℝ := z.re
  by_cases hpole : a = 0 ∧ b = 0
  · have him : z.im = Real.exp (-1 : ℝ) := by
      have he : Real.exp (1 : ℝ) ≠ 0 := (Real.exp_pos 1).ne'
      have ha : Real.exp (1 : ℝ) * z.im = 1 := by
        dsimp [a] at hpole
        linarith [hpole.1]
      rw [Real.exp_neg, ← one_div]
      exact (eq_div_iff he).2 (by simpa [mul_comm] using ha)
    have hz : z = verticalPath (-1) := by
      apply UpperHalfPlane.ext_re_im
      · simpa [verticalPath, b] using hpole.2
      · simpa [verticalPath] using him
    refine ⟨IsometryEquiv.constSMul
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) ModularGroup.S), ?_, ?_⟩
    · rw [← verticalPath_zero_eq_I]
      change (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S • verticalPath 0 : H2) =
        verticalPath 0
      have hh := modular_S_verticalPath 0
      change (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S • verticalPath 0 : H2) =
        verticalPath (-0) at hh
      simpa only [neg_zero] using hh
    · rw [hz]
      change (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S • verticalPath 1 : H2) =
        verticalPath (-1)
      exact modular_S_verticalPath 1
  · have hab : 0 < a ^ 2 + b ^ 2 := by
      by_contra hn
      have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
      have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
      exact hpole ⟨ha, hb⟩
    refine ⟨IsometryEquiv.constSMul (stabilizerRotation a b hab), ?_, ?_⟩
    · exact stabilizerRotation_fixes_I a b hab
    · exact stabilizerRotation_maps_vertical_one z h hab

theorem exists_ordered_pair_isometry (x y : H2) (hxy : dist x y = 1) :
    ∃ e : H2 ≃ᵢ H2, e UpperHalfPlane.I = x ∧
      e (verticalPath 1) = y := by
  let e₀ : H2 ≃ᵢ H2 :=
    IsometryEquiv.constSMul x.toSL2R
  have he₀ : e₀ UpperHalfPlane.I = x := by
    change (x.toSL2R • UpperHalfPlane.I : H2) = x
    exact x.toSL2R_smul_I
  let w : H2 := e₀.symm y
  have hw : dist UpperHalfPlane.I w = 1 := by
    have hdist := e₀.isometry.dist_eq UpperHalfPlane.I (e₀.symm y)
    rw [e₀.apply_symm_apply, he₀] at hdist
    simpa [w, hxy] using hdist.symm
  obtain ⟨s, hsI, hs1⟩ := exists_stabilizer_map_vertical_one w hw
  refine ⟨s.trans e₀, ?_, ?_⟩
  · rw [IsometryEquiv.trans_apply, hsI, he₀]
  · rw [IsometryEquiv.trans_apply, hs1]
    exact e₀.apply_symm_apply y

end CurveComplex.Hyperbolic
