import CurveComplexGenusTwo.Hyperbolic.Stabilizer
open scoped UpperHalfPlane MatrixGroups
open Matrix
namespace CurveComplex.Hyperbolic

theorem actual_normalized_boundary_axes_common_perpendicular (d : ℝ) (hd : 0 ≤ d) :
 let D : ℝ → SL(2,ℝ) := fun s =>
   ⟨!![Real.exp (s/2),0;0,Real.exp (-(s/2))], by simp [Matrix.det_fin_two, ←Real.exp_add]⟩
 let J : SL(2,ℝ) := ⟨!![0,-1;1,0], by simp [Matrix.det_fin_two]⟩
 let R : SL(2,ℝ) := stabilizerRotation 1 1 (by norm_num)
 Isometry (fun t : ℝ => D (-d/2) • (R • verticalPath t)) ∧
 Isometry (fun t : ℝ => D (d/2) • (R • verticalPath t)) ∧
 (∀ t : ℝ, J • (D (-d/2) • (R • verticalPath t)) =
   D (d/2) • (R • verticalPath (-t))) ∧
 (∀ s t : ℝ, d ≤ dist (D (-d/2) • (R • verticalPath s)) (D (d/2) • (R • verticalPath t))) ∧
 dist (D (-d/2) • (R • verticalPath 0)) (D (d/2) • (R • verticalPath 0)) = d := by
 dsimp only
 let D : ℝ → SL(2,ℝ) := fun s =>
   ⟨!![Real.exp (s/2),0;0,Real.exp (-(s/2))], by simp [Matrix.det_fin_two, ←Real.exp_add]⟩
 let J : SL(2,ℝ) := ⟨!![0,-1;1,0], by simp [Matrix.det_fin_two]⟩
 let R : SL(2,ℝ) := stabilizerRotation 1 1 (by norm_num)
 have hJD (s : ℝ) : J * D s = D (-s) * J := by
  apply Subtype.ext
  change J.val * (D s).val = (D (-s)).val * J.val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J,D,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two] <;> ring
 have hJR : J * R = R * J := by
  apply Subtype.ext
  change J.val * R.val = R.val * J.val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J,R,stabilizerRotation,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,one_div] <;> ring
 have hJv (t : ℝ) : J • verticalPath t = verticalPath (-t) := by
  apply UpperHalfPlane.coe_injective
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [J,verticalPath,UpperHalfPlane.num,UpperHalfPlane.denom]
  apply Complex.ext
  · simp [Complex.div_re,Complex.normSq_apply]
  · simp [Complex.div_im,Complex.normSq_apply,Real.exp_neg]
    field_simp [Real.exp_ne_zero]

 have hnearest (z w : UpperHalfPlane) (r R : ℝ) (hr : 0 < r) (hR : 0 < R)
     (hn : Complex.normSq (z : ℂ) = r^2)
     (hm : Complex.normSq (w : ℂ) = R^2) :
     dist (UpperHalfPlane.mk ⟨0,r⟩ hr) (UpperHalfPlane.mk ⟨0,R⟩ hR) ≤ dist z w := by
   have hc (x y u v r R : ℝ) (hr : 0 < r) (hR : 0 < R)
       (hy : 0 < y) (hv : 0 < v)
       (hn : x^2+y^2=r^2) (hm : u^2+v^2=R^2) :
       (r^2+R^2-2*x*u)*(r*R) ≥ (r^2+R^2)*(y*v) := by
     have hyr : y ≤ r := by nlinarith [sq_nonneg x]
     have hvR : v ≤ R := by nlinarith [sq_nonneg u]
     have hyv : y*v ≤ r*R := mul_le_mul hyr hvR hv.le hr.le
     have hidentity : (r*R)^2-(x*u+y*v)^2=(x*v-y*u)^2 := by
       calc
         (r*R)^2-(x*u+y*v)^2 = (x^2+y^2)*(u^2+v^2)-(x*u+y*v)^2 := by rw [hn,hm];ring
         _ = (x*v-y*u)^2 := by ring
     have habs : |x*u+y*v| ≤ r*R := by
       apply (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ r*R)).mp
       rw [sq_abs]
       nlinarith [sq_nonneg (x*v-y*u)]
     have hdot : x*u+y*v ≤ r*R := (le_abs_self _).trans habs
     have hK : 2*(r*R) ≤ r^2+R^2 := by nlinarith [sq_nonneg (r-R)]
     have hg : 0 ≤ r*R-y*v := by linarith
     have hout : 2*(r*R)*(x*u) ≤ (r^2+R^2)*(r*R-y*v) := by
       by_cases hp : 0 ≤ x*u
       · calc
           2*(r*R)*(x*u) ≤ 2*(r*R)*(r*R-y*v) :=
             mul_le_mul_of_nonneg_left (by linarith) (by positivity)
           _ ≤ (r^2+R^2)*(r*R-y*v) := mul_le_mul_of_nonneg_right hK hg
       · exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_ge hp)).trans
           (mul_nonneg (by positivity) hg)
     nlinarith [hout]
   have hz : z.re^2+z.im^2=r^2 := by simpa [Complex.normSq_apply, pow_two] using hn
   have hw : w.re^2+w.im^2=R^2 := by simpa [Complex.normSq_apply, pow_two] using hm
   have hbound := hc z.re z.im w.re w.im r R hr hR z.im_pos w.im_pos hz hw
   have hnum : (z.re-w.re)^2+z.im^2+w.im^2=r^2+R^2-2*z.re*w.re := by nlinarith
   have hh : Real.cosh (dist (UpperHalfPlane.mk ⟨0,r⟩ hr) (UpperHalfPlane.mk ⟨0,R⟩ hR)) ≤ Real.cosh (dist z w) := by
     rw [UpperHalfPlane.cosh_dist', UpperHalfPlane.cosh_dist']
     simp only [UpperHalfPlane.mk_re, UpperHalfPlane.mk_im, zero_sub, sub_zero,
       sub_self, zero_pow (by norm_num : (2:ℕ)≠0), zero_add]
     rw [hnum]
     apply (div_le_div_iff₀ (by positivity : 0 < 2*r*R)
       (by positivity : 0 < 2*z.im*w.im)).mpr
     nlinarith [hbound]
   simpa only [abs_of_nonneg dist_nonneg] using Real.cosh_le_cosh.mp hh
 have hscale (s : ℝ) (z : UpperHalfPlane) :
     ((D s • z : UpperHalfPlane) : ℂ) = (Real.exp s : ℂ) * z := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [D, UpperHalfPlane.num, UpperHalfPlane.denom]
  rw [div_eq_mul_inv, ←Complex.exp_neg]
  simp only [neg_neg]
  rw [mul_right_comm, ←Complex.exp_add]
  congr 2
  ring
 have hcircle (t : ℝ) : Complex.normSq ((R • verticalPath t : UpperHalfPlane) : ℂ) = 1 := by
  rw [stabilizerRotation_coe_smul]
  simp [Complex.normSq_div, Complex.normSq_apply, verticalPath,
    Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  positivity
 have hnorm (s t : ℝ) :
     Complex.normSq ((D s • (R • verticalPath t) : UpperHalfPlane) : ℂ) = (Real.exp s)^2 := by
   rw [hscale,Complex.normSq_mul,hcircle]
   simp [Complex.normSq_apply,pow_two,Complex.exp_ofReal_re]
 have hzero (s : ℝ) : D s • (R • verticalPath 0) = verticalPath s := by
   have hv0 : verticalPath 0 = UpperHalfPlane.I := by
     apply UpperHalfPlane.ext_re_im <;> simp [verticalPath]
   rw [hv0]
   have hRI : R • UpperHalfPlane.I = UpperHalfPlane.I := stabilizerRotation_fixes_I 1 1 _
   rw [hRI]
   apply UpperHalfPlane.coe_injective
   rw [hscale]
   apply Complex.ext <;> simp [verticalPath,Complex.exp_ofReal_re]
 have hdistzero : dist (D (-d/2) • (R • verticalPath 0))
     (D (d/2) • (R • verticalPath 0)) = d := by
   rw [hzero,hzero,verticalPath_isometry.dist_eq,Real.dist_eq]
   rw [show -d/2-d/2 = -d by ring, abs_neg,abs_of_nonneg hd]
 refine ⟨?_,?_,?_,?_,hdistzero⟩
 · exact (IsometryEquiv.constSMul (D (-d/2))).isometry.comp
     ((IsometryEquiv.constSMul R).isometry.comp verticalPath_isometry)
 · exact (IsometryEquiv.constSMul (D (d/2))).isometry.comp
     ((IsometryEquiv.constSMul R).isometry.comp verticalPath_isometry)
 · intro t
   change J • (D (-d/2) • (R • verticalPath t)) = D (d/2) • (R • verticalPath (-t))
   rw [←mul_smul,hJD,mul_smul,←mul_smul J R,hJR,mul_smul,hJv]
   congr 2 <;> ring
 · intro s t
   have h := hnearest (D (-d/2) • (R • verticalPath s))
     (D (d/2) • (R • verticalPath t)) (Real.exp (-d/2)) (Real.exp (d/2))
     (Real.exp_pos _) (Real.exp_pos _) (hnorm _ _) (hnorm _ _)
   have hl : UpperHalfPlane.mk ⟨0,Real.exp (-d/2)⟩ (Real.exp_pos _) = verticalPath (-d/2) := rfl
   have hr : UpperHalfPlane.mk ⟨0,Real.exp (d/2)⟩ (Real.exp_pos _) = verticalPath (d/2) := rfl
   rw [hl,hr,verticalPath_isometry.dist_eq,Real.dist_eq] at h
   rw [show -d/2-d/2 = -d by ring, abs_neg,abs_of_nonneg hd] at h
   exact h

theorem actual_normalized_equal_boundary_generator_exchange (d L : ℝ) :
 let D : ℝ → SL(2,ℝ) := fun s =>
   ⟨!![Real.exp (s/2),0;0,Real.exp (-(s/2))], by simp [Matrix.det_fin_two, ←Real.exp_add]⟩
 let J : SL(2,ℝ) := ⟨!![0,-1;1,0], by simp [Matrix.det_fin_two]⟩
 let R : SL(2,ℝ) := stabilizerRotation 1 1 (by norm_num)
 let A := D (-d/2) * R * D L * R⁻¹ * D (d/2)
 let B := D (d/2) * R * D (-L) * R⁻¹ * D (-d/2)
 J * A * J⁻¹ = B ∧ J * B * J⁻¹ = A := by
 dsimp only
 let D : ℝ → SL(2,ℝ) := fun s =>
   ⟨!![Real.exp (s/2),0;0,Real.exp (-(s/2))], by simp [Matrix.det_fin_two, ←Real.exp_add]⟩
 let J : SL(2,ℝ) := ⟨!![0,-1;1,0], by simp [Matrix.det_fin_two]⟩
 let R : SL(2,ℝ) := stabilizerRotation 1 1 (by norm_num)
 have hJD (s : ℝ) : J * D s = D (-s) * J := by
  apply Subtype.ext
  change J.val * (D s).val = (D (-s)).val * J.val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J,D,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two] <;> ring
 have hJR : J * R = R * J := by
  apply Subtype.ext
  change J.val * R.val = R.val * J.val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J,R,stabilizerRotation,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,one_div] <;> ring
 let A := D (-d/2) * R * D L * R⁻¹ * D (d/2)
 let B := D (d/2) * R * D (-L) * R⁻¹ * D (-d/2)
 have hJRinv : J * R⁻¹ = R⁻¹ * J := (show Commute J R from hJR).inv_right.eq
 have hex (s q : ℝ) :
     J * (D (-s/2) * R * D q * R⁻¹ * D (s/2)) =
       (D (s/2) * R * D (-q) * R⁻¹ * D (-s/2)) * J := by
   calc
     J * (D (-s/2) * R * D q * R⁻¹ * D (s/2)) =
         D (s/2) * (J * R) * D q * R⁻¹ * D (s/2) := by
       rw [←mul_assoc, ←mul_assoc, ←mul_assoc, ←mul_assoc, hJD]
       simp only [neg_div, neg_neg]
       group
     _ = D (s/2) * R * (J * D q) * R⁻¹ * D (s/2) := by rw [hJR];group
     _ = D (s/2) * R * D (-q) * (J * R⁻¹) * D (s/2) := by rw [hJD];group
     _ = (D (s/2) * R * D (-q) * R⁻¹ * D (-s/2)) * J := by
       rw [hJRinv]
       simp only [mul_assoc]
       rw [hJD]
       simp only [neg_div]
 constructor
 · change J * A * J⁻¹ = B
   have h := hex d L
   change J * A = B * J at h
   rw [h]
   group
 · change J * B * J⁻¹ = A
   have h := hex (-d) (-L)
   simp only [neg_div, neg_neg] at h
   have h' : J * B = A * J := by simpa only [A,B,neg_div,neg_neg] using h
   rw [h']
   group

end CurveComplex.Hyperbolic
