import CurveComplexGenusTwo.Topology.ActualGeometryRelease.ActualHyperbolicComponentCoverPlanePROVED
import CurveComplexGenusTwo.Hyperbolic.VerticalRigidity
import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints

namespace CurveComplex.Hyperbolic

open Matrix
open scoped MatrixGroups

-- Candidate classification package, pending bounded statement review.
noncomputable def axisZeroReflection : H2 ≃ᵢ H2 := by
  let F : H2 → H2 := fun z => ⟨-star (z : ℂ), by simpa using z.im_pos⟩
  have hinv : Function.Involutive F := by
    intro z
    apply UpperHalfPlane.coe_injective
    simp [F]
  refine { toEquiv := hinv.toPerm F, isometry_toFun := ?_ }
  apply Isometry.of_dist_eq
  intro z w
  change dist (F z) (F w) = dist z w
  simp only [F, UpperHalfPlane.dist_eq, UpperHalfPlane.mk_im,
    Complex.neg_im, Complex.star_def, Complex.conj_im, neg_neg, dist_neg_neg,
    Complex.dist_conj_conj, UpperHalfPlane.coe_im]

@[simp]
theorem axisZeroReflection_re (z : H2) :
    (axisZeroReflection z).re = -z.re := by
  change (-star (z : ℂ)).re = -z.re
  simp

@[simp]
theorem axisZeroReflection_im (z : H2) :
    (axisZeroReflection z).im = z.im := by
  change (-star (z : ℂ)).im = z.im
  simp

@[simp]
theorem axisZeroReflection_I :
    axisZeroReflection UpperHalfPlane.I = UpperHalfPlane.I := by
  apply UpperHalfPlane.ext_re_im <;> simp

@[simp]
theorem axisZeroReflection_vertical (t : ℝ) :
    axisZeroReflection (verticalPath t) = verticalPath t := by
  apply UpperHalfPlane.ext_re_im <;> simp [verticalPath]

theorem axis_equal_distance_cross (z w a : H2) (h : dist z a = dist w a) :
    ((z.re - a.re)^2 + z.im^2 + a.im^2) * w.im =
      ((w.re - a.re)^2 + w.im^2 + a.im^2) * z.im := by
  have hc := congrArg Real.cosh h
  rw [UpperHalfPlane.cosh_dist', UpperHalfPlane.cosh_dist'] at hc
  have hc' := (div_eq_div_iff
    (by positivity : 2*z.im*a.im ≠ 0)
    (by positivity : 2*w.im*a.im ≠ 0)).mp hc
  apply mul_right_cancel₀ a.im_ne_zero
  nlinarith only [hc']

theorem axis_three_anchor_uniqueness (z w : H2)
    (h0 : dist z UpperHalfPlane.I = dist w UpperHalfPlane.I)
    (h1 : dist z (verticalPath 1) = dist w (verticalPath 1))
    (ha : dist z (⟨(1 : ℂ) + Complex.I, by simp⟩ : H2) =
      dist w (⟨(1 : ℂ) + Complex.I, by simp⟩ : H2)) : z = w := by
  have hI := axis_equal_distance_cross z w UpperHalfPlane.I h0
  have hV := axis_equal_distance_cross z w (verticalPath 1) h1
  have hA := axis_equal_distance_cross z w (⟨(1 : ℂ) + Complex.I, by simp⟩ : H2) ha
  simp only [UpperHalfPlane.I_re, UpperHalfPlane.I_im, sub_zero, one_pow] at hI
  simp only [verticalPath, UpperHalfPlane.mk_re, UpperHalfPlane.mk_im] at hV
  simp only [UpperHalfPlane.mk_re, UpperHalfPlane.mk_im, Complex.add_re,
    Complex.add_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
    add_zero, zero_add, one_pow] at hA
  have hprod : ((Real.exp (1 : ℝ))^2-1)*(w.im-z.im) = 0 := by
    nlinarith only [hI,hV]
  have hn : (Real.exp (1 : ℝ))^2-1 ≠ 0 := by
    have he := Real.one_lt_exp_iff.mpr (show (0 : ℝ) < 1 by norm_num)
    nlinarith [sq_nonneg (Real.exp (1 : ℝ)-1)]
  have him : z.im = w.im := by
    have hh := (mul_eq_zero.mp hprod).resolve_left hn
    linarith
  rw [← him] at hI hA
  have hnorm : z.re^2+z.im^2+1 = w.re^2+z.im^2+1 :=
    mul_right_cancel₀ z.im_ne_zero hI
  have hnorm' : (z.re-1)^2+z.im^2+1 = (w.re-1)^2+z.im^2+1 :=
    mul_right_cancel₀ z.im_ne_zero hA
  have hre : z.re = w.re := by nlinarith only [hnorm,hnorm']
  exact UpperHalfPlane.ext_re_im hre him

theorem axis_two_anchor_coordinates (z w : H2)
    (h0 : dist z UpperHalfPlane.I = dist w UpperHalfPlane.I)
    (h1 : dist z (verticalPath 1) = dist w (verticalPath 1)) :
    z.im = w.im ∧ z.re^2 = w.re^2 := by
  have hI := axis_equal_distance_cross z w UpperHalfPlane.I h0
  have hV := axis_equal_distance_cross z w (verticalPath 1) h1
  simp only [UpperHalfPlane.I_re, UpperHalfPlane.I_im, sub_zero, one_pow] at hI
  simp only [verticalPath, UpperHalfPlane.mk_re, UpperHalfPlane.mk_im] at hV
  have hprod : ((Real.exp (1 : ℝ))^2-1)*(w.im-z.im) = 0 := by
    nlinarith only [hI,hV]
  have hn : (Real.exp (1 : ℝ))^2-1 ≠ 0 := by
    have he := Real.one_lt_exp_iff.mpr (show (0 : ℝ) < 1 by norm_num)
    nlinarith [sq_nonneg (Real.exp (1 : ℝ)-1)]
  have him : z.im = w.im := by
    have hh := (mul_eq_zero.mp hprod).resolve_left hn
    linarith
  refine ⟨him, ?_⟩
  rw [← him] at hI
  have hnorm := mul_right_cancel₀ z.im_ne_zero hI
  linarith

theorem axis_normalized_isometry_identity_or_reflection (f : H2 ≃ᵢ H2)
    (hI : f UpperHalfPlane.I = UpperHalfPlane.I)
    (hV : f (verticalPath 1) = verticalPath 1) :
    (∀ z, f z = z) ∨ (∀ z, f z = axisZeroReflection z) := by
  let a : H2 := ⟨(1 : ℂ)+Complex.I, by simp⟩
  have h0 : dist (f a) UpperHalfPlane.I = dist a UpperHalfPlane.I := by
    simpa only [hI] using f.isometry.dist_eq a UpperHalfPlane.I
  have h1 : dist (f a) (verticalPath 1) = dist a (verticalPath 1) := by
    simpa only [hV] using f.isometry.dist_eq a (verticalPath 1)
  obtain ⟨him, hsq⟩ := axis_two_anchor_coordinates (f a) a h0 h1
  have hsq' : (f a).re^2 = 1 := by simpa [a] using hsq
  have hfactor : ((f a).re-1)*((f a).re+1) = 0 := by nlinarith only [hsq']
  rcases mul_eq_zero.mp hfactor with hpos | hneg
  · have hfa : f a = a := by
      apply UpperHalfPlane.ext_re_im
      · have hre : (f a).re = 1 := by linarith
        simpa [a] using hre
      · exact him
    left
    intro z
    apply axis_three_anchor_uniqueness (f z) z
    · simpa only [hI] using f.isometry.dist_eq z UpperHalfPlane.I
    · simpa only [hV] using f.isometry.dist_eq z (verticalPath 1)
    · simpa only [hfa] using f.isometry.dist_eq z a
  · have hfa : f a = axisZeroReflection a := by
      apply UpperHalfPlane.ext_re_im
      · simp only [axisZeroReflection_re]
        have hre : (f a).re = -1 := by linarith
        simpa [a] using hre
      · simpa only [axisZeroReflection_im] using him
    right
    intro z
    have hdI : dist (f z) UpperHalfPlane.I = dist (axisZeroReflection z) UpperHalfPlane.I := by
      calc
        dist (f z) UpperHalfPlane.I = dist z UpperHalfPlane.I := by
          simpa only [hI] using f.isometry.dist_eq z UpperHalfPlane.I
        _ = dist (axisZeroReflection z) UpperHalfPlane.I := by
          simpa only [axisZeroReflection_I] using
            (axisZeroReflection.isometry.dist_eq z UpperHalfPlane.I).symm
    have hdV : dist (f z) (verticalPath 1) = dist (axisZeroReflection z) (verticalPath 1) := by
      calc
        dist (f z) (verticalPath 1) = dist z (verticalPath 1) := by
          simpa only [hV] using f.isometry.dist_eq z (verticalPath 1)
        _ = dist (axisZeroReflection z) (verticalPath 1) := by
          simpa only [axisZeroReflection_vertical] using
            (axisZeroReflection.isometry.dist_eq z (verticalPath 1)).symm
    have hd := f.isometry.dist_eq z a
    rw [hfa] at hd
    have hr := axisZeroReflection.isometry.dist_eq z a
    have h0 := axis_two_anchor_coordinates (f z) (axisZeroReflection z) hdI hdV
    have hc := axis_equal_distance_cross (f z) (axisZeroReflection z)
      (axisZeroReflection a) (hd.trans hr.symm)
    have hi := h0.1
    rw [← hi] at hc
    have hc' := mul_right_cancel₀ (f z).im_ne_zero hc
    simp only [axisZeroReflection_re, axisZeroReflection_im] at h0 hc'
    have haRe : a.re = 1 := by simp [a]
    rw [haRe] at hc'
    have hre : (f z).re = -z.re := by nlinarith only [h0.2,hc']
    exact UpperHalfPlane.ext_re_im (by simpa only [axisZeroReflection_re] using hre) hi

theorem axis_exists_stabilizer_matrix (z : H2) (h : dist UpperHalfPlane.I z = 1) :
    ∃ A : SL(2, ℝ), (A • UpperHalfPlane.I : H2) = UpperHalfPlane.I ∧
      (A • verticalPath 1 : H2) = z := by
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
    let S : SL(2, ℝ) := Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) ModularGroup.S
    refine ⟨S, ?_, ?_⟩
    · have hzero : verticalPath 0 = UpperHalfPlane.I := by
        apply UpperHalfPlane.ext_re_im <;> simp [verticalPath]
      rw [← hzero]
      have hh := modular_S_verticalPath 0
      change (S • verticalPath 0 : H2) = verticalPath (-0) at hh
      simpa only [neg_zero] using hh
    · rw [hz]
      exact modular_S_verticalPath 1
  · have hab : 0 < a^2 + b^2 := by
      by_contra hn
      have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
      have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
      exact hpole ⟨ha,hb⟩
    exact ⟨stabilizerRotation a b hab, stabilizerRotation_fixes_I a b hab,
      stabilizerRotation_maps_vertical_one z h hab⟩

theorem axis_exists_ordered_pair_matrix (x y : H2) (hxy : dist x y = 1) :
    ∃ A : SL(2, ℝ), (A • UpperHalfPlane.I : H2) = x ∧
      (A • verticalPath 1 : H2) = y := by
  let A₀ := x.toSL2R
  let e₀ : H2 ≃ᵢ H2 := IsometryEquiv.constSMul A₀
  have he₀ : e₀ UpperHalfPlane.I = x := x.toSL2R_smul_I
  let w : H2 := e₀.symm y
  have hw : dist UpperHalfPlane.I w = 1 := by
    have hdist := e₀.isometry.dist_eq UpperHalfPlane.I (e₀.symm y)
    rw [e₀.apply_symm_apply, he₀] at hdist
    simpa [w, hxy] using hdist.symm
  obtain ⟨A, hAI, hAV⟩ := axis_exists_stabilizer_matrix w hw
  refine ⟨A₀ * A, ?_, ?_⟩
  · rw [mul_smul, hAI]
    exact x.toSL2R_smul_I
  · rw [mul_smul, hAV]
    exact e₀.apply_symm_apply y

theorem axis_metric_isometry_mobius_or_antimobius (g : H2 ≃ᵢ H2) :
    ∃ A : SL(2, ℝ),
      (∀ z : H2, g z = A • z) ∨
      (∀ z : H2, g z = A • axisZeroReflection z) := by
  have hzero : verticalPath 0 = UpperHalfPlane.I := by
    apply UpperHalfPlane.ext_re_im <;> simp [verticalPath]
  have hp : dist (g UpperHalfPlane.I) (g (verticalPath 1)) = 1 := by
    rw [g.isometry.dist_eq, ← hzero, verticalPath_isometry.dist_eq]
    norm_num
  obtain ⟨A,hAI,hAV⟩ := axis_exists_ordered_pair_matrix
    (g UpperHalfPlane.I) (g (verticalPath 1)) hp
  let e : H2 ≃ᵢ H2 := IsometryEquiv.constSMul A
  let f : H2 ≃ᵢ H2 := g.trans e.symm
  have hfI : f UpperHalfPlane.I = UpperHalfPlane.I := by
    change e.symm (g UpperHalfPlane.I) = UpperHalfPlane.I
    change e UpperHalfPlane.I = g UpperHalfPlane.I at hAI
    rw [← hAI, e.symm_apply_apply]
  have hfV : f (verticalPath 1) = verticalPath 1 := by
    change e.symm (g (verticalPath 1)) = verticalPath 1
    change e (verticalPath 1) = g (verticalPath 1) at hAV
    rw [← hAV, e.symm_apply_apply]
  refine ⟨A, ?_⟩
  rcases axis_normalized_isometry_identity_or_reflection f hfI hfV with hid | href
  · left
    intro z
    have h := congrArg e (hid z)
    simpa only [f, IsometryEquiv.trans_apply, e.apply_symm_apply, e,
      IsometryEquiv.constSMul_apply] using h
  · right
    intro z
    have h := congrArg e (href z)
    simpa only [f, IsometryEquiv.trans_apply, e.apply_symm_apply, e,
      IsometryEquiv.constSMul_apply] using h

theorem axis_metric_isometry_gl_representation (g : H2 ≃ᵢ H2) :
    ∃ A : GL (Fin 2) ℝ, ∀ z : H2, g z = A • z := by
  obtain ⟨A, hA | hA⟩ := axis_metric_isometry_mobius_or_antimobius g
  · refine ⟨SpecialLinearGroup.mapGL ℝ A, ?_⟩
    intro z
    exact hA z
  · refine ⟨SpecialLinearGroup.mapGL ℝ A * UpperHalfPlane.J, ?_⟩
    intro z
    rw [mul_smul, hA]
    congr 1
    apply UpperHalfPlane.coe_injective
    rw [UpperHalfPlane.coe_J_smul]
    rfl

theorem axis_uniform_gl_no_fixed (A : GL (Fin 2) ℝ) (ε : ℝ) (hε : 0 < ε)
    (hdisp : ∀ z : H2, ε ≤ dist z (A • z)) :
    ∀ z : H2, A • z ≠ z := by
  intro z hz
  have h := hdisp z
  rw [hz, dist_self] at h
  linarith

theorem axis_uniform_gl_discriminant_nonneg (A : GL (Fin 2) ℝ)
    (ε : ℝ) (hε : 0 < ε) (hdisp : ∀ z : H2, ε ≤ dist z (A • z)) :
    0 ≤ A.val.discr := by
  by_contra h
  have hell : A.val.IsElliptic := lt_of_not_ge h
  have hpos : 0 < A.val.det := by
    rw [Matrix.IsElliptic, Matrix.discr_fin_two] at hell
    nlinarith [sq_nonneg A.val.trace]
  have hfixed := (UpperHalfPlane.gl_smul_eq_self_iff_eq_fixedPt hpos hell).mpr
    (rfl : UpperHalfPlane.fixedPt A hell = UpperHalfPlane.fixedPt A hell)
  exact axis_uniform_gl_no_fixed A ε hε hdisp _ hfixed

theorem axis_uniform_gl_negative_trace_ne_zero (A : GL (Fin 2) ℝ)
    (hdet : A.val.det < 0) (ε : ℝ) (hε : 0 < ε)
    (hdisp : ∀ z : H2, ε ≤ dist z (A • z)) : A.val.trace ≠ 0 := by
  intro htrace
  obtain ⟨z,hz⟩ := (UpperHalfPlane.exists_gl_smul_eq_self_iff_trace_eq_zero hdet).mpr htrace
  exact axis_uniform_gl_no_fixed A ε hε hdisp z hz

theorem axis_gl_cosh_displacement_positive (A : GL (Fin 2) ℝ)
    (hdet : 0 < A.val.det) (z : H2) :
    Real.cosh (dist z (A • z)) = 1 +
      ((A 1 0 * (z.re^2 - z.im^2) + (A 1 1 - A 0 0) * z.re - A 0 1)^2 +
        ((2*A 1 0*z.re + A 1 1 - A 0 0)*z.im)^2) /
      (2*A.val.det*z.im^2) := by
  rw [UpperHalfPlane.cosh_dist]
  have him := UpperHalfPlane.im_smul_eq_div_normSq A z
  rw [GeneralLinearGroup.val_det_apply] at him
  rw [abs_of_pos hdet] at him
  rw [him, UpperHalfPlane.coe_smul_of_det_pos (by simpa using hdet)]
  rw [dist_eq_norm, ← Complex.normSq_eq_norm_sq]
  have hden := UpperHalfPlane.denom_ne_zero A z
  have hd : Complex.normSq (UpperHalfPlane.denom A z) ≠ 0 :=
    (Complex.normSq_pos.mpr hden).ne'
  have hcomplex : (z : ℂ) - UpperHalfPlane.num A z / UpperHalfPlane.denom A z =
      ((z : ℂ) * UpperHalfPlane.denom A z - UpperHalfPlane.num A z) /
        UpperHalfPlane.denom A z := by
    field_simp
  rw [hcomplex, Complex.normSq_div]
  have hcancel (N : ℝ) :
      (N / Complex.normSq (UpperHalfPlane.denom A z)) /
        (2*z.im*(A.val.det*z.im/Complex.normSq (UpperHalfPlane.denom A z))) =
      N/(2*A.val.det*z.im^2) := by
    field_simp [hd, hdet.ne', z.im_ne_zero]
    <;> ring
  rw [hcancel]
  congr 2
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, add_zero, zero_add, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

theorem axis_uniform_gl_cosh_lower (A : GL (Fin 2) ℝ) (ε : ℝ) (hε : 0 < ε)
    (hdisp : ∀ z : H2, ε ≤ dist z (A • z)) (z : H2) :
    Real.cosh ε ≤ Real.cosh (dist z (A • z)) := by
  apply Real.cosh_le_cosh.mpr
  simpa only [abs_of_pos hε, abs_of_nonneg dist_nonneg] using hdisp z

theorem axis_uniform_gl_discriminant_pos (A : GL (Fin 2) ℝ)
    (ε : ℝ) (hε : 0 < ε) (hdisp : ∀ z : H2, ε ≤ dist z (A • z)) :
    0 < A.val.discr := by
  have hnonneg := axis_uniform_gl_discriminant_nonneg A ε hε hdisp
  by_contra hpos
  have hdisc : A.val.discr = 0 := le_antisymm (le_of_not_gt hpos) hnonneg
  have hdet : 0 < A.val.det := by
    have hn := A.det_ne_zero
    rw [Matrix.discr_fin_two] at hdisc
    have hge : 0 ≤ A.val.det := by nlinarith [sq_nonneg A.val.trace]
    exact lt_of_le_of_ne hge hn.symm
  let δ := Real.cosh ε - 1
  have hδ : 0 < δ := sub_pos.mpr (Real.one_lt_cosh.mpr hε.ne')
  have hrel : (A 0 0 - A 1 1)^2 + 4*A 0 1*A 1 0 = 0 := by
    rw [Matrix.discr_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two] at hdisc
    nlinarith only [hdisc]
  by_cases hc : A 1 0 = 0
  · have had : A 0 0 = A 1 1 := by rw [hc] at hrel; nlinarith only [hrel]
    let y := Real.sqrt ((A 0 1^2 + 1)/(A.val.det*δ))
    have hy : 0 < y := Real.sqrt_pos.mpr (div_pos (by positivity) (mul_pos hdet hδ))
    have hysq : y^2 = (A 0 1^2 + 1)/(A.val.det*δ) :=
      Real.sq_sqrt (by positivity)
    have hyrel : A.val.det*δ*y^2 = A 0 1^2 + 1 := by
      rw [hysq]
      field_simp
    let z : H2 := ⟨⟨0,y⟩,hy⟩
    have hcosh := axis_gl_cosh_displacement_positive A hdet z
    simp only [z, UpperHalfPlane.mk_re, UpperHalfPlane.mk_im, hc, had,
      zero_mul, mul_zero, sub_self, zero_sub, neg_sq, zero_add, add_zero, zero_pow
      (by norm_num : (2 : ℕ) ≠ 0)] at hcosh
    have hbound : A 0 1^2/(2*A.val.det*y^2) ≤ δ/2 := by
      apply (div_le_iff₀ (by positivity : 0 < 2*A.val.det*y^2)).mpr
      nlinarith only [hyrel]
    have hlow := axis_uniform_gl_cosh_lower A ε hε hdisp z
    rw [hcosh] at hlow
    dsimp [δ] at hbound hδ
    linarith
  · let x := (A 0 0-A 1 1)/(2*A 1 0)
    have hx : 2*A 1 0*x = A 0 0-A 1 1 := by dsimp [x]; field_simp
    have hxroot : A 1 0*x^2 + (A 1 1-A 0 0)*x-A 0 1 = 0 := by
      dsimp [x]
      field_simp
      linear_combination (-1)*hrel
    let y := Real.sqrt (A.val.det*δ/(A 1 0^2+1))
    have hy : 0 < y := Real.sqrt_pos.mpr (div_pos (mul_pos hdet hδ) (by positivity))
    have hysq : y^2 = A.val.det*δ/(A 1 0^2+1) := Real.sq_sqrt (by positivity)
    have hyrel : y^2*(A 1 0^2+1) = A.val.det*δ := by rw [hysq]; field_simp
    let z : H2 := ⟨⟨x,y⟩,hy⟩
    have hreal : A 1 0*(x^2-y^2)+(A 1 1-A 0 0)*x-A 0 1 = -A 1 0*y^2 := by
      linear_combination hxroot
    have himag : 2*A 1 0*x+A 1 1-A 0 0 = 0 := by linarith only [hx]
    have hcosh := axis_gl_cosh_displacement_positive A hdet z
    simp only [z, UpperHalfPlane.mk_re, UpperHalfPlane.mk_im, hreal, himag,
      zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] at hcosh
    have hfrac : (-A 1 0*y^2)^2/(2*A.val.det*y^2) = A 1 0^2*y^2/(2*A.val.det) := by
      field_simp
      <;> ring
    rw [hfrac] at hcosh
    have hbound : A 1 0^2*y^2/(2*A.val.det) ≤ δ/2 := by
      apply (div_le_iff₀ (by positivity : 0 < 2*A.val.det)).mpr
      nlinarith only [hyrel, sq_nonneg y]
    have hlow := axis_uniform_gl_cosh_lower A ε hε hdisp z
    rw [hcosh] at hlow
    dsimp [δ] at hbound hδ
    linarith

open Matrix
open scoped MatrixGroups

-- Elementary two-dimensional diagonalization, pending bounded statement review.
theorem axis_discriminant_positive_diagonalization (A : GL (Fin 2) ℝ)
    (hdiscr : 0 < A.val.discr) :
    ∃ (T : SL(2, ℝ)) (r s : ℝ), r ≠ 0 ∧ s ≠ 0 ∧
      A.val * T.val = T.val * !![r,0;0,s] := by
  let a := A 0 0
  let b := A 0 1
  let c := A 1 0
  let d := A 1 1
  have hdet : a*d-b*c ≠ 0 := by
    simpa only [Matrix.det_fin_two] using A.det_ne_zero
  by_cases hc : c = 0
  · have had : d-a ≠ 0 := by
      intro h
      have heq : d = a := sub_eq_zero.mp h
      simp only [Matrix.discr_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two] at hdiscr
      change 0 < (a+d)^2-4*(a*d-b*c) at hdiscr
      rw [hc,heq] at hdiscr
      nlinarith only [hdiscr]
    have ha : a ≠ 0 := by intro ha; rw [ha,hc] at hdet; simp at hdet
    have hd : d ≠ 0 := by intro hd; rw [hd,hc] at hdet; simp at hdet
    let u := b/(d-a)
    let T : SL(2, ℝ) := ⟨!![1,u;0,1], by simp [Matrix.det_fin_two]⟩
    refine ⟨T,a,d,ha,hd,?_⟩
    have hu : a*u+b = u*d := by dsimp [u]; field_simp; ring
    have hA10 : A 1 0 = 0 := hc
    have hA01 : A 0 0*u+A 0 1 = u*A 1 1 := hu
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [T, Matrix.mul_apply, Fin.sum_univ_two, hA10, hA01, a, d]
  · let q := Real.sqrt A.val.discr
    have hq : 0 < q := Real.sqrt_pos.mpr hdiscr
    have hqsq : q^2 = (a-d)^2+4*b*c := by
      have hs := Real.sq_sqrt hdiscr.le
      dsimp [q]
      rw [hs, Matrix.discr_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
      dsimp [a,b,c,d]
      ring
    let p := (a-d+q)/2
    let m := (a-d-q)/2
    let r := (a+d+q)/2
    let s := (a+d-q)/2
    have hrs : r*s = a*d-b*c := by dsimp [r,s]; nlinarith only [hqsq]
    have hr : r ≠ 0 := by intro hr; rw [hr,zero_mul] at hrs; exact hdet hrs.symm
    have hs : s ≠ 0 := by intro hs; rw [hs,mul_zero] at hrs; exact hdet hrs.symm
    have hpr : a*p+b*c = p*r := by dsimp [p,r]; nlinarith only [hqsq]
    have hcr : c*p+d*c = c*r := by dsimp [p,r]; ring
    have hms : a*m+b*c = m*s := by dsimp [m,s]; nlinarith only [hqsq]
    have hcs : c*m+d*c = c*s := by dsimp [m,s]; ring
    let T : SL(2, ℝ) := ⟨!![p/(c*q),m;c/(c*q),c], by
      simp only [Matrix.det_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      dsimp [p,m]
      field_simp [hc, hq.ne']
      <;> ring⟩
    refine ⟨T,r,s,hr,hs,?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [T, Matrix.mul_apply, Fin.sum_univ_two]
    · change a*(p/(c*q))+b*(c/(c*q)) = p/(c*q)*r
      field_simp [hc,hq.ne']
      simpa only [mul_comm c b] using hpr
    · exact hms
    · change c*(p/(c*q))+d*(c/(c*q)) = c/(c*q)*r
      field_simp [hc,hq.ne']
      dsimp [p,r]
      ring
    · exact hcs

noncomputable def axisDiagonalMatrix (r s : ℝ) (hr : r ≠ 0) (hs : s ≠ 0) :
    GL (Fin 2) ℝ := GeneralLinearGroup.mkOfDetNeZero !![r,0;0,s] (by simp [hr,hs])

theorem axis_diagonal_vertical_translation (r s : ℝ) (hr : r ≠ 0) (hs : s ≠ 0)
    (t : ℝ) :
    (axisDiagonalMatrix r s hr hs • verticalPath t : H2) =
      verticalPath (t + Real.log |r/s|) := by
  have hratio : 0 < |r/s| := abs_pos.mpr (div_ne_zero hr hs)
  apply UpperHalfPlane.ext_re_im
  · rw [UpperHalfPlane.re_smul]
    simp [axisDiagonalMatrix, UpperHalfPlane.num, UpperHalfPlane.denom, verticalPath,
      Complex.div_re, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  · rw [UpperHalfPlane.im_smul_eq_div_normSq]
    simp only [GeneralLinearGroup.val_det_apply, axisDiagonalMatrix,
      GeneralLinearGroup.mkOfDetNeZero, Units.val_mk, Matrix.det_fin_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul, sub_zero,
      UpperHalfPlane.denom, Complex.normSq_apply]
    simp [verticalPath, Real.exp_add, Real.exp_log hratio, abs_mul, abs_div]
    have hsa : |s| ≠ 0 := abs_ne_zero.mpr hs
    have hsq : s^2 = |s|^2 := (sq_abs s).symm
    rw [Real.exp_log (div_pos (abs_pos.mpr hr) (abs_pos.mpr hs)), ←pow_two s, hsq]
    field_simp [hsa]
    <;> ring

theorem axis_discriminant_positive_translated_anchors (A : GL (Fin 2) ℝ)
    (hdiscr : 0 < A.val.discr) :
    ∃ (e : H2 ≃ᵢ H2) (c : ℝ),
      (A • e (verticalPath 0) : H2) = e (verticalPath c) ∧
      (A • e (verticalPath 1) : H2) = e (verticalPath (1+c)) := by
  obtain ⟨T,r,s,hr,hs,hmat⟩ := axis_discriminant_positive_diagonalization A hdiscr
  let D := axisDiagonalMatrix r s hr hs
  let Tgl := SpecialLinearGroup.mapGL ℝ T
  have hgl : A*Tgl = Tgl*D := by
    apply Units.ext
    change A.val*T.val = T.val*!![r,0;0,s]
    exact hmat
  let e : H2 ≃ᵢ H2 := IsometryEquiv.constSMul T
  have hline (t : ℝ) : (A • e (verticalPath t) : H2) =
      e (verticalPath (t+Real.log |r/s|)) := by
    change A • (Tgl • verticalPath t) = Tgl • verticalPath (t+Real.log |r/s|)
    rw [←mul_smul,hgl,mul_smul]
    exact congrArg (fun z : H2 => Tgl • z) (axis_diagonal_vertical_translation r s hr hs t)
  refine ⟨e,Real.log |r/s|,?_,hline 1⟩
  simpa only [zero_add] using hline 0

-- Candidate helper: pending statement review. Not the original theorem.
theorem translated_vertical_axis_of_two_anchors
    (g e : H2 ≃ᵢ H2) (c : ℝ)
    (h0 : g (e (verticalPath 0)) = e (verticalPath c))
    (h1 : g (e (verticalPath 1)) = e (verticalPath (1 + c))) :
    ∀ t : ℝ, g (e (verticalPath t)) = e (verticalPath (t + c)) := by
  let F : ℝ → H2 := fun t => e.symm (g (e (verticalPath t)))
  have hF : Isometry F := e.symm.isometry.comp
    (g.isometry.comp (e.isometry.comp verticalPath_isometry))
  -- Translate the output along the vertical axis using a dilation.
  let d : H2 ≃ᵢ H2 := {
    toFun := fun z => (⟨Real.exp (-c), Real.exp_pos (-c)⟩ : {a : ℝ // 0 < a}) • z
    invFun := fun z => (⟨Real.exp c, Real.exp_pos c⟩ : {a : ℝ // 0 < a}) • z
    left_inv := by
      intro z
      apply UpperHalfPlane.ext_re_im <;>
        simp [← mul_assoc, ← Real.exp_add]
    right_inv := by
      intro z
      apply UpperHalfPlane.ext_re_im <;>
        simp [← mul_assoc, ← Real.exp_add]
    isometry_toFun := UpperHalfPlane.isometry_pos_mul
      ⟨Real.exp (-c), Real.exp_pos (-c)⟩ }
  have hd (t : ℝ) : d (verticalPath t) = verticalPath (t - c) := by
    apply UpperHalfPlane.ext_re_im
    · simp [d, verticalPath]
    · simp [d, verticalPath, Real.exp_sub, Real.exp_neg, div_eq_mul_inv, mul_comm]
  have hN : Isometry (fun t : ℝ => d (F t)) := d.isometry.comp hF
  have hN0 : d (F 0) = verticalPath 0 := by
    dsimp [F]
    rw [h0, e.symm_apply_apply, hd]
    simp
  have hN1 : d (F 1) = verticalPath 1 := by
    dsimp [F]
    rw [h1, e.symm_apply_apply, hd]
    simp
  intro t
  have h := isometry_eq_vertical_of_values _ hN hN0 hN1 t
  have h' : d (F t) = d (verticalPath (t + c)) := by
    rw [h, hd]
    simp
  have h'' := d.injective h'
  simpa only [F, e.apply_symm_apply] using congrArg e h''

-- Candidate reduction: its extra anchor premises must still be produced.
theorem positive_axis_of_translated_vertical_anchors
    (g : H2 ≃ᵢ H2) (ε : ℝ) (hε : 0 < ε)
    (hdisplacement : ∀ z : H2, ε ≤ dist z (g z))
    (e : H2 ≃ᵢ H2) (c : ℝ)
    (h0 : g (e (verticalPath 0)) = e (verticalPath c))
    (h1 : g (e (verticalPath 1)) = e (verticalPath (1 + c))) :
    ∃ axis : ℝ → H2, Isometry axis ∧
      ∃ period : ℝ, 0 < period ∧
        ∀ t : ℝ, g (axis t) = axis (t + period) := by
  have hc : c ≠ 0 := by
    intro hc
    have h := hdisplacement (e (verticalPath 0))
    rw [h0, hc, dist_self] at h
    linarith
  have hline := translated_vertical_axis_of_two_anchors g e c h0 h1
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · refine ⟨fun t => e (verticalPath (-t)),
      e.isometry.comp (verticalPath_isometry.comp
        (Isometry.of_dist_eq (fun x y : ℝ => by simp [Real.dist_eq]))),
      -c, neg_pos.mpr hneg, ?_⟩
    intro t
    change g (e (verticalPath (-t))) = e (verticalPath (-(t + -c)))
    rw [hline]
    congr 2
    ring
  · exact ⟨fun t => e (verticalPath t), e.isometry.comp verticalPath_isometry,
      c, hpos, hline⟩

open scoped UpperHalfPlane

/-- Source Fact 3.5(G1), elementary axis step. Positive uniform displacement
is to be derived from the actual compact quotient's uniform covering radius;
no axis or displacement minimizer is assumed. Orientation reversing glide
translations are allowed. -/
theorem actual_hyperbolic_isometry_axis_of_uniform_displacement
    (g : H2 ≃ᵢ H2) (ε : ℝ) (hε : 0 < ε)
    (hdisplacement : ∀ z : H2, ε ≤ dist z (g z)) :
    ∃ axis : ℝ → H2, Isometry axis ∧
      ∃ period : ℝ, 0 < period ∧
        ∀ t : ℝ, g (axis t) = axis (t + period) := by
  obtain ⟨A,hA⟩ := axis_metric_isometry_gl_representation g
  have hdispA (z : H2) : ε ≤ dist z (A • z) := by
    rw [← hA]
    exact hdisplacement z
  have hdiscr := axis_uniform_gl_discriminant_pos A ε hε hdispA
  obtain ⟨e,c,h0,h1⟩ := axis_discriminant_positive_translated_anchors A hdiscr
  have hg0 : g (e (verticalPath 0)) = e (verticalPath c) := by
    rw [hA]
    exact h0
  have hg1 : g (e (verticalPath 1)) = e (verticalPath (1+c)) := by
    rw [hA]
    exact h1
  exact positive_axis_of_translated_vertical_anchors g ε hε hdisplacement e c hg0 hg1

end CurveComplex.Hyperbolic
