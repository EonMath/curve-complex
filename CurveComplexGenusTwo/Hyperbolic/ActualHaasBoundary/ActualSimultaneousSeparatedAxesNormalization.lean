import CurveComplexGenusTwo.Hyperbolic.Stabilizer
import CurveComplexGenusTwo.Hyperbolic.VerticalRigidity
import CurveComplexGenusTwo.Hyperbolic.VerticalProjection
open scoped UpperHalfPlane MatrixGroups
open Matrix
namespace CurveComplex.Hyperbolic
set_option maxHeartbeats 10000000

/-- Actual ultraparallel complete H2 geodesics admit the common-perpendicular
normal form used in Haas–Susskind Lemma1. Uniform positive distance excludes
asymptotic axes; no exchanging symmetry or quotient involution is assumed. -/
private theorem axis_normalization_private_sl_normal_form
    (a b : ℝ → UpperHalfPlane) (ha : Isometry a) (hb : Isometry b)
    (hsep : ∃ ε : ℝ, 0 < ε ∧ ∀ s t : ℝ, ε ≤ dist (a s) (b t)) :
    let D : ℝ → SL(2,ℝ) := fun s =>
      ⟨!![Real.exp (s/2),0;0,Real.exp (-(s/2))], by
        simp [Matrix.det_fin_two, ←Real.exp_add]⟩
    let R : SL(2,ℝ) := stabilizerRotation 1 1 (by norm_num)
    ∃ (d : ℝ) (u : SL(2,ℝ)), 0 < d ∧
      Set.range a = Set.range (fun t : ℝ => u • (D (-d/2) • (R • verticalPath t))) ∧
      Set.range b = Set.range (fun t : ℝ => u • (D (d/2) • (R • verticalPath t))) := by
  dsimp only
  let D : ℝ → SL(2,ℝ) := fun s =>
    ⟨!![Real.exp (s/2),0;0,Real.exp (-(s/2))],by simp [Matrix.det_fin_two,←Real.exp_add]⟩
  let R : SL(2,ℝ) := stabilizerRotation 1 1 (by norm_num)
  have minimum (a b : ℝ → H2) (ha : Isometry a) (hb : Isometry b)
      (hsep : ∃ ε : ℝ, 0 < ε ∧ ∀ s t : ℝ, ε ≤ dist (a s) (b t)) :
      ∃ s₀ t₀ : ℝ, 0 < dist (a s₀) (b t₀) ∧
        ∀ s t : ℝ, dist (a s₀) (b t₀) ≤ dist (a s) (b t) := by
    have normalize (a : ℝ → H2) (ha : Isometry a) :
        ∃ g : SL(2,ℝ), ∀ t, a t = g • verticalPath t := by
      have verticalPath_zero_eq_I : verticalPath 0 = UpperHalfPlane.I := by
        apply UpperHalfPlane.ext
        apply Complex.ext <;> simp [verticalPath,UpperHalfPlane.I]
      have stabilize (z : H2) (h : dist UpperHalfPlane.I z = 1) :
          ∃ s : SL(2,ℝ), s • UpperHalfPlane.I = UpperHalfPlane.I ∧ s • verticalPath 1 = z := by
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
          refine ⟨(Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) ModularGroup.S), ?_, ?_⟩
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
          refine ⟨stabilizerRotation a b hab, ?_, ?_⟩
          · exact stabilizerRotation_fixes_I a b hab
          · exact stabilizerRotation_maps_vertical_one z h hab
      let e₀ : H2 ≃ᵢ H2 := IsometryEquiv.constSMul (a 0).toSL2R
      have he₀ : e₀ UpperHalfPlane.I = a 0 := (a 0).toSL2R_smul_I
      let w : H2 := e₀.symm (a 1)
      have hw : dist UpperHalfPlane.I w = 1 := by
        have hd := e₀.dist_eq UpperHalfPlane.I (e₀.symm (a 1))
        rw [e₀.apply_symm_apply,he₀,ha.dist_eq] at hd
        simpa [w,Real.dist_eq] using hd.symm
      obtain ⟨s,hs0,hs1⟩ := stabilize w hw
      let g : SL(2,ℝ) := (a 0).toSL2R * s
      let e : H2 ≃ᵢ H2 := IsometryEquiv.constSMul g
      have he0 : e (verticalPath 0) = a 0 := by
        change g • verticalPath 0 = a 0
        rw [verticalPath_zero_eq_I]
        dsimp [g]
        rw [mul_smul,hs0]
        exact (a 0).toSL2R_smul_I
      have he1 : e (verticalPath 1) = a 1 := by
        change g • verticalPath 1 = a 1
        dsimp [g]
        rw [mul_smul,hs1]
        exact e₀.apply_symm_apply (a 1)
      have hf : Isometry (fun t : ℝ => e.symm (a t)) := e.symm.isometry.comp ha
      have hf0 : e.symm (a 0) = verticalPath 0 := by rw [←he0,e.symm_apply_apply]
      have hf1 : e.symm (a 1) = verticalPath 1 := by rw [←he1,e.symm_apply_apply]
      refine ⟨g,?_⟩
      intro t
      have ht := isometry_eq_vertical_of_values _ hf hf0 hf1 t
      have heq : a t = e (verticalPath t) := by
        simpa only [e.apply_symm_apply] using congrArg e ht
      exact heq
    have ratio (g : SL(2,ℝ)) (t : ℝ) :
        (g • verticalPath t).re / (g • verticalPath t).im =
          g 0 0 * g 1 0 * Real.exp t + g 0 1 * g 1 1 / Real.exp t := by
      have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
        have h := g.property
        change Matrix.det (g.val) = 1 at h
        rw [Matrix.det_fin_two] at h
        exact h
      have hnorm : (g 1 0 * Real.exp t)^2 + (g 1 1)^2 ≠ 0 := by
        intro hz
        have hc : g 1 0 = 0 := by
          have hh : g 1 0 * Real.exp t = 0 := by nlinarith [sq_nonneg (g 1 1)]
          exact (mul_eq_zero.mp hh).resolve_right (Real.exp_ne_zero t)
        have hd : g 1 1 = 0 := by nlinarith [sq_nonneg (g 1 0 * Real.exp t)]
        rw [hc,hd] at hdet
        norm_num at hdet
      have hcoords := UpperHalfPlane.coe_specialLinearGroup_apply g (verticalPath t)
      have hre := congrArg Complex.re hcoords
      have him := congrArg Complex.im hcoords
      simp only [UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,
        Algebra.algebraMap_self,Complex.div_re,Complex.div_im,
        Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
        Complex.ofReal_re,Complex.ofReal_im,verticalPath,
        UpperHalfPlane.coe_mk,Complex.normSq_apply] at hre him
      simp only [RingHom.id_apply,mul_zero,zero_mul,add_zero,zero_add,sub_zero] at hre him
      dsimp only [verticalPath]
      rw [hre,him]
      field_simp [hnorm,Real.exp_ne_zero]
      have hden : g 1 1 * g 0 0 - g 0 1 * g 1 0 = 1 := by nlinarith [hdet]
      rw [hden]
      have hn : g 1 1 ^ 2 + g 1 0 ^ 2 * Real.exp t ^ 2 ≠ 0 := by
        convert hnorm using 1 <;> ring
      field_simp [hn]
      ring
    have projection_distance (x : H2) :
        Real.cosh (dist x (verticalProjection x)) ^ 2 = 1 + (x.re/x.im)^2 := by
      have hn : 0 < ‖(x : ℂ)‖ := by
        apply norm_pos_iff.mpr
        intro h
        have hh := congrArg Complex.im h
        have hp := x.im_pos
        simp at hh
        linarith
      have hnorm : ‖(x : ℂ)‖^2 = x.re^2+x.im^2 := by
        rw [Complex.sq_norm,Complex.normSq_apply]
        change x.re*x.re+x.im*x.im = x.re^2+x.im^2
        ring
      have hc : Real.cosh (dist x (verticalProjection x)) = ‖(x:ℂ)‖/x.im := by
        rw [UpperHalfPlane.cosh_dist']
        simp only [verticalProjection,verticalProjectionParameter,verticalPath,
          UpperHalfPlane.mk_re,UpperHalfPlane.mk_im,Real.exp_log hn,
          sub_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0)]
        field_simp [x.im_ne_zero,hn.ne']
        nlinarith [hnorm]
      rw [hc]
      field_simp [x.im_ne_zero]
      nlinarith [hnorm]
    have positive_product (A B k : ℝ) (hk : 0 < k)
        (hbound : ∀ y : ℝ, 0 < y → k ≤ (A*y+B/y)^2) : 0 < A*B := by
      have tiny (C : ℝ) : ∃ y : ℝ, 0 < y ∧ (C/y)^2 < k := by
        let h := C^2/k
        have hh : 0 ≤ h := div_nonneg (sq_nonneg _) hk.le
        let y := h+1
        have hy : 0 < y := by dsimp [y];linarith
        have hc : C^2 = k*h := by dsimp [h];field_simp
        have hs : h < y^2 := by dsimp [y];nlinarith [sq_nonneg h]
        refine ⟨y,hy,?_⟩
        rw [div_pow]
        apply (div_lt_iff₀ (sq_pos_of_pos hy)).mpr
        rw [hc]
        exact mul_lt_mul_of_pos_left hs hk
      by_cases ha : A = 0
      · obtain ⟨y,hy,hsmall⟩ := tiny B
        have hh := hbound y hy
        simp only [ha,zero_mul,zero_add] at hh
        exact False.elim (not_le_of_gt hsmall hh)
      by_cases hb : B = 0
      · obtain ⟨y,hy,hsmall⟩ := tiny A
        have hh := hbound y⁻¹ (inv_pos.mpr hy)
        simp only [hb,zero_div,add_zero,←div_eq_mul_inv] at hh
        exact False.elim (not_le_of_gt hsmall hh)
      by_contra hprod
      have hneg : A*B < 0 := lt_of_le_of_ne (le_of_not_gt hprod) (mul_ne_zero ha hb)
      have hratio : 0 < -B/A := by
        rcases mul_neg_iff.mp hneg with ⟨hA,hB⟩ | ⟨hA,hB⟩
        · exact div_pos (neg_pos.mpr hB) hA
        · exact div_pos_of_neg_of_neg (neg_neg_of_pos hB) hA
      let r := Real.sqrt (-B/A)
      have hr : 0 < r := Real.sqrt_pos.mpr hratio
      have hrr : A*r^2 = -B := by
        rw [show r^2 = -B/A from Real.sq_sqrt hratio.le]
        field_simp [ha]
      have hz : A*r+B/r = 0 := by
        field_simp [hr.ne']
        nlinarith [hrr]
      have hh := hbound r hr
      rw [hz] at hh
      norm_num at hh
      linarith
    have scalar_minimum (A B : ℝ) (hprod : 0 < A*B) :
        ∃ t : ℝ, ∀ u : ℝ,
          |A*Real.exp t+B/Real.exp t| ≤ |A*Real.exp u+B/Real.exp u| := by
      have ha : A ≠ 0 := by intro h;rw [h,zero_mul] at hprod;linarith
      have hratio : 0 < B/A := by
        rcases mul_pos_iff.mp hprod with ⟨ha,hb⟩ | ⟨ha,hb⟩
        · exact div_pos hb ha
        · exact div_pos_of_neg_of_neg hb ha
      let r := Real.sqrt (B/A)
      have hr : 0 < r := Real.sqrt_pos.mpr hratio
      have hrr : A*r^2 = B := by
        rw [show r^2 = B/A from Real.sq_sqrt hratio.le]
        field_simp [ha]
      have hequal : A*r = B/r := (eq_div_iff hr.ne').mpr (by nlinarith [hrr])
      have hbase : (A*r+B/r)^2 = 4*A*B := by
        rw [←hequal]
        calc
          (A*r+A*r)^2 = 4*A*(A*r^2) := by ring
          _ = 4*A*B := by rw [hrr]
      have hmin (y : ℝ) (hy : 0 < y) : |A*r+B/r| ≤ |A*y+B/y| := by
        have hid : (A*y+B/y)^2 -4*A*B = (A*y-B/y)^2 := by
          field_simp
          ring
        apply (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mp
        simp only [sq_abs]
        nlinarith [sq_nonneg (A*y-B/y)]
      refine ⟨Real.log r,?_⟩
      intro u
      rw [Real.exp_log hr]
      exact hmin (Real.exp u) (Real.exp_pos u)
    obtain ⟨g₀,hg₀⟩ := normalize a ha
    obtain ⟨g₁,hg₁⟩ := normalize b hb
    let g := g₀⁻¹*g₁
    let e : H2 ≃ᵢ H2 := IsometryEquiv.constSMul g₀
    let z : ℝ → H2 := fun t => g • verticalPath t
    have ez (t : ℝ) : e (z t) = b t := by
      change g₀ • ((g₀⁻¹*g₁) • verticalPath t) = b t
      rw [←mul_smul,←mul_assoc,mul_inv_cancel,one_mul,←hg₁]
    have ea (s : ℝ) : e (verticalPath s) = a s := (hg₀ s).symm
    obtain ⟨ε,hε,hseparated⟩ := hsep
    have normalized_sep (s t : ℝ) : ε ≤ dist (verticalPath s) (z t) := by
      have hd := e.dist_eq (verticalPath s) (z t)
      rw [ea,ez] at hd
      exact hd ▸ hseparated s t
    let k := Real.cosh ε ^2-1
    have hk : 0 < k := by
      have hcosh := Real.one_lt_cosh.mpr hε.ne'
      dsimp [k]
      nlinarith
    have hbound (y : ℝ) (hy : 0 < y) :
        k ≤ (g 0 0*g 1 0*y+g 0 1*g 1 1/y)^2 := by
      let t := Real.log y
      have hh : ε ≤ dist (z t) (verticalProjection (z t)) := by
        simpa only [verticalProjection,dist_comm] using
          normalized_sep (verticalProjectionParameter (z t)) t
      have hc : Real.cosh ε ≤ Real.cosh (dist (z t) (verticalProjection (z t))) :=
        Real.cosh_le_cosh.mpr (by rwa [abs_of_pos hε,abs_of_nonneg dist_nonneg])
      have hd := projection_distance (z t)
      have hr := ratio g t
      change (z t).re/(z t).im = _ at hr
      rw [hr,show Real.exp t=y from Real.exp_log hy] at hd
      dsimp [k]
      nlinarith [Real.cosh_pos ε,Real.cosh_pos (dist (z t) (verticalProjection (z t)))]
    have hprod := positive_product (g 0 0*g 1 0) (g 0 1*g 1 1) k hk hbound
    obtain ⟨t₀,ht₀⟩ := scalar_minimum (g 0 0*g 1 0) (g 0 1*g 1 1) hprod
    let s₀ := verticalProjectionParameter (z t₀)
    have hmin (t : ℝ) : dist (z t₀) (verticalProjection (z t₀)) ≤
        dist (z t) (verticalProjection (z t)) := by
      have hratio := ht₀ t
      have hr0 := ratio g t₀
      have hrt := ratio g t
      change (z t₀).re/(z t₀).im = _ at hr0
      change (z t).re/(z t).im = _ at hrt
      rw [←hr0,←hrt] at hratio
      have hsquare := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hratio
      simp only [sq_abs] at hsquare
      have hd0 := projection_distance (z t₀)
      have hdt := projection_distance (z t)
      have hc : Real.cosh (dist (z t₀) (verticalProjection (z t₀))) ≤
          Real.cosh (dist (z t) (verticalProjection (z t))) := by
        nlinarith [Real.cosh_pos (dist (z t₀) (verticalProjection (z t₀))),
          Real.cosh_pos (dist (z t) (verticalProjection (z t)))]
      simpa only [abs_of_nonneg dist_nonneg] using Real.cosh_le_cosh.mp hc
    refine ⟨s₀,t₀,lt_of_lt_of_le hε (hseparated _ _),?_⟩
    intro s t
    have hp := verticalProjection_nearest (z t) s
    have hh := (hmin t).trans hp
    have hd0 := e.dist_eq (verticalPath s₀) (z t₀)
    have hdt := e.dist_eq (verticalPath s) (z t)
    rw [ea,ez] at hd0 hdt
    rw [hd0,hdt]
    simpa only [s₀,verticalProjection,dist_comm] using hh
  have align (x y : H2) (r : ℝ) (hr : 0 < r) (hxy : dist x y = r) :
      ∃ g : SL(2,ℝ), g • UpperHalfPlane.I = x ∧ g • verticalPath r = y := by
    have verticalPath_zero_eq_I : verticalPath 0 = UpperHalfPlane.I := by
      apply UpperHalfPlane.ext
      apply Complex.ext <;> simp [verticalPath,UpperHalfPlane.I]
    have denominator (a b : ℝ) (hab : 0 < a^2+b^2) (w : H2) :
        (-(b : ℂ)*(w:ℂ)+a) ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp [Complex.mul_im] at him
      have hb : b=0 := by
        rcases him with hb | hw
        · exact hb
        · exact (w.im_pos.ne' hw).elim
      have ha : a≠0 := by
        intro ha;rw [ha,hb] at hab;norm_num at hab
      exact ha (by simpa [hb] using h)
    have sphere (z : H2) (h : dist UpperHalfPlane.I z = r) :
        Real.exp r*(z.re^2+z.im^2+1) = z.im*(1+(Real.exp r)^2) := by
      have hstd : dist (verticalPath 0) (verticalPath r) = r := by
        rw [verticalPath_isometry.dist_eq]
        simp [Real.dist_eq,abs_of_pos hr]
      have hc := congrArg Real.cosh (h.trans (verticalPath_zero_eq_I ▸ hstd).symm)
      rw [UpperHalfPlane.cosh_dist',UpperHalfPlane.cosh_dist'] at hc
      simp only [verticalPath,UpperHalfPlane.mk_re,UpperHalfPlane.mk_im] at hc
      simp only [UpperHalfPlane.I_re,UpperHalfPlane.I_im,zero_sub,neg_sq,
        one_pow,zero_pow (by norm_num : (2:ℕ) ≠ 0)] at hc
      field_simp at hc
      nlinarith [hc]
    have rotation (z : H2) (h : dist UpperHalfPlane.I z = r)
        (hab : 0 < (1-Real.exp r*z.im)^2+z.re^2) :
        stabilizerRotation (1-Real.exp r*z.im) z.re hab • verticalPath r = z := by
      let a := 1 - Real.exp r * z.im
      let b := z.re
      have hsphere := sphere z h
      have hEim : (Complex.exp (r : ℂ)).im = 0 := by
        simpa using Complex.exp_ofReal_im r
      have hEre : (Complex.exp (r : ℂ)).re = Real.exp r := by
        simpa using Complex.exp_ofReal_re r
      apply UpperHalfPlane.coe_injective
      rw [stabilizerRotation_coe_smul]
      apply (div_eq_iff (denominator a b hab (verticalPath r))).2
      apply Complex.ext
      · simp [verticalPath, Complex.add_re, Complex.mul_re, Complex.neg_re,
          Complex.mul_im, Complex.neg_im]
        dsimp [a, b]
        ring
      · simp [verticalPath, Complex.add_im, Complex.mul_im, Complex.neg_im,
          Complex.mul_re, Complex.neg_re]
        dsimp [a, b]
        simp only [hEre]
        nlinarith [hsphere]
    have stabilize (z : H2) (h : dist UpperHalfPlane.I z = r) :
        ∃ s : SL(2,ℝ), s • UpperHalfPlane.I = UpperHalfPlane.I ∧ s • verticalPath r = z := by
      let a : ℝ := 1 - Real.exp r * z.im
      let b : ℝ := z.re
      by_cases hpole : a = 0 ∧ b = 0
      · have him : z.im = Real.exp (-r) := by
          have he : Real.exp r ≠ 0 := (Real.exp_pos r).ne'
          have ha : Real.exp r * z.im = 1 := by
            dsimp [a] at hpole
            linarith [hpole.1]
          rw [Real.exp_neg, ← one_div]
          exact (eq_div_iff he).2 (by simpa [mul_comm] using ha)
        have hz : z = verticalPath (-r) := by
          apply UpperHalfPlane.ext_re_im
          · simpa [verticalPath, b] using hpole.2
          · simpa [verticalPath] using him
        refine ⟨(Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) ModularGroup.S), ?_, ?_⟩
        · rw [← verticalPath_zero_eq_I]
          change (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S • verticalPath 0 : H2) =
            verticalPath 0
          have hh := modular_S_verticalPath 0
          change (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S • verticalPath 0 : H2) =
            verticalPath (-0) at hh
          simpa only [neg_zero] using hh
        · rw [hz]
          change (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S • verticalPath r : H2) =
            verticalPath (-r)
          exact modular_S_verticalPath r
      · have hab : 0 < a ^ 2 + b ^ 2 := by
          by_contra hn
          have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
          have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
          exact hpole ⟨ha, hb⟩
        refine ⟨stabilizerRotation a b hab, ?_, ?_⟩
        · exact stabilizerRotation_fixes_I a b hab
        · exact rotation z h hab
    let e₀ : H2 ≃ᵢ H2 := IsometryEquiv.constSMul x.toSL2R
    have he₀ : e₀ UpperHalfPlane.I = x := x.toSL2R_smul_I
    let w := e₀.symm y
    have hw : dist UpperHalfPlane.I w = r := by
      have hd := e₀.dist_eq UpperHalfPlane.I (e₀.symm y)
      rw [e₀.apply_symm_apply,he₀,hxy] at hd
      exact hd.symm
    obtain ⟨s,hs0,hsr⟩ := stabilize w hw
    refine ⟨x.toSL2R*s,?_,?_⟩
    · rw [mul_smul,hs0]
      exact x.toSL2R_smul_I
    · rw [mul_smul,hsr]
      exact e₀.apply_symm_apply y
  have normalize (a : ℝ → H2) (ha : Isometry a) :
      ∃ g : SL(2,ℝ), ∀ t, a t = g • verticalPath t := by
    have verticalPath_zero_eq_I : verticalPath 0 = UpperHalfPlane.I := by
      apply UpperHalfPlane.ext
      apply Complex.ext <;> simp [verticalPath,UpperHalfPlane.I]
    have stabilize (z : H2) (h : dist UpperHalfPlane.I z = 1) :
        ∃ s : SL(2,ℝ), s • UpperHalfPlane.I = UpperHalfPlane.I ∧ s • verticalPath 1 = z := by
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
        refine ⟨(Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) ModularGroup.S), ?_, ?_⟩
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
        refine ⟨stabilizerRotation a b hab, ?_, ?_⟩
        · exact stabilizerRotation_fixes_I a b hab
        · exact stabilizerRotation_maps_vertical_one z h hab
    let e₀ : H2 ≃ᵢ H2 := IsometryEquiv.constSMul (a 0).toSL2R
    have he₀ : e₀ UpperHalfPlane.I = a 0 := (a 0).toSL2R_smul_I
    let w : H2 := e₀.symm (a 1)
    have hw : dist UpperHalfPlane.I w = 1 := by
      have hd := e₀.dist_eq UpperHalfPlane.I (e₀.symm (a 1))
      rw [e₀.apply_symm_apply,he₀,ha.dist_eq] at hd
      simpa [w,Real.dist_eq] using hd.symm
    obtain ⟨s,hs0,hs1⟩ := stabilize w hw
    let g : SL(2,ℝ) := (a 0).toSL2R * s
    let e : H2 ≃ᵢ H2 := IsometryEquiv.constSMul g
    have he0 : e (verticalPath 0) = a 0 := by
      change g • verticalPath 0 = a 0
      rw [verticalPath_zero_eq_I]
      dsimp [g]
      rw [mul_smul,hs0]
      exact (a 0).toSL2R_smul_I
    have he1 : e (verticalPath 1) = a 1 := by
      change g • verticalPath 1 = a 1
      dsimp [g]
      rw [mul_smul,hs1]
      exact e₀.apply_symm_apply (a 1)
    have hf : Isometry (fun t : ℝ => e.symm (a t)) := e.symm.isometry.comp ha
    have hf0 : e.symm (a 0) = verticalPath 0 := by rw [←he0,e.symm_apply_apply]
    have hf1 : e.symm (a 1) = verticalPath 1 := by rw [←he1,e.symm_apply_apply]
    refine ⟨g,?_⟩
    intro t
    have ht := isometry_eq_vertical_of_values _ hf hf0 hf1 t
    have heq : a t = e (verticalPath t) := by
      simpa only [e.apply_symm_apply] using congrArg e ht
    exact heq
  have orthogonal_square (g : SL(2,ℝ)) (d : ℝ) (hd : d ≠ 0)
      (hfix : g • UpperHalfPlane.I = UpperHalfPlane.I)
      (hmin : ∀ t : ℝ, dist (verticalPath d) UpperHalfPlane.I ≤
        dist (verticalPath d) (g • verticalPath t)) : g 0 0 ^2 = g 0 1 ^2 := by
    have norm_formula (g : SL(2,ℝ)) (t : ℝ) :
        ‖((g • verticalPath t : H2) : ℂ)‖^2 =
          (g 0 0 ^2 * Real.exp t ^2+g 0 1 ^2) /
          (g 1 0 ^2 * Real.exp t ^2+g 1 1 ^2) := by
      rw [Complex.sq_norm,UpperHalfPlane.coe_specialLinearGroup_apply,Complex.normSq_div]
      simp only [Algebra.algebraMap_self,RingHom.id_apply,Complex.normSq_apply,
        Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
        Complex.ofReal_re,Complex.ofReal_im,verticalPath,UpperHalfPlane.coe_mk]
      simp only [mul_zero,zero_mul,zero_add,add_zero]
      congr 1 <;> ring
    have hdet : g 0 0*g 1 1-g 0 1*g 1 0=1 := by
      have h:=g.property
      change Matrix.det g.val=1 at h
      rw [Matrix.det_fin_two] at h
      exact h
    have hden : ((g 1 0:ℂ)*Complex.I+g 1 1) ≠ 0 := by
      intro h
      have hr:=congrArg Complex.re h
      have hi:=congrArg Complex.im h
      simp at hr hi
      rw [hr,hi] at hdet
      norm_num at hdet
    have hcoeff := congrArg (fun z : H2 => (z:ℂ)) hfix
    rw [UpperHalfPlane.coe_specialLinearGroup_apply] at hcoeff
    simp only [Algebra.algebraMap_self,RingHom.id_apply,UpperHalfPlane.coe_I] at hcoeff
    have hcross := (div_eq_iff hden).mp hcoeff
    have hre:=congrArg Complex.re hcross
    have him:=congrArg Complex.im hcross
    simp at hre him
    have hgc : g 1 0 = -g 0 1 := by linarith [hre]
    have hga : g 1 1 = g 0 0 := him.symm
    have hunit : g 0 0 ^2+g 0 1 ^2=1 := by rw [hgc,hga] at hdet;nlinarith [hdet]
    let e : H2 ≃ᵢ H2 := IsometryEquiv.constSMul g
    let w := e.symm (verticalPath d)
    have hnormpos : 0 < ‖(w:ℂ)‖ := by
      apply norm_pos_iff.mpr
      intro h
      have hi:=congrArg Complex.im h
      have hp:=w.im_pos
      simp at hi
      linarith
    have hdist (t : ℝ) : dist w (verticalPath t) = dist (verticalPath d) (g • verticalPath t) := by
      have h:=e.dist_eq w (verticalPath t)
      rw [show e w=verticalPath d from e.apply_symm_apply _] at h
      exact h.symm
    have hclosest : dist w (verticalPath 0) ≤ dist w (verticalProjection w) := by
      change dist w (verticalPath 0) ≤ dist w (verticalPath (verticalProjectionParameter w))
      rw [hdist,hdist]
      have hv0 : verticalPath 0=UpperHalfPlane.I := by
        apply UpperHalfPlane.ext_re_im <;> simp [verticalPath]
      rw [hv0,hfix]
      exact hmin _
    have hparam:=verticalProjection_unique w 0 hclosest
    have hwnorm : ‖(w:ℂ)‖=1 := by
      have h:=congrArg Real.exp hparam
      rw [Real.exp_zero,show Real.exp (verticalProjectionParameter w)=‖(w:ℂ)‖ from Real.exp_log hnormpos] at h
      exact h.symm
    have hw : w=g⁻¹ • verticalPath d := by rfl
    have hn:=norm_formula g⁻¹ d
    rw [←hw,hwnorm,one_pow] at hn
    simp only [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,
      Matrix.cons_val_zero,Matrix.cons_val_one] at hn
    rw [hgc,hga] at hn
    norm_num at hn
    have hdenom : g 0 1 ^2*Real.exp d ^2+g 0 0 ^2 ≠ 0 := by
      intro h
      have hb : g 0 1=0 := by
        have hb2 : g 0 1 ^2=0 := by nlinarith [sq_nonneg (g 0 0),sq_pos_of_pos (Real.exp_pos d)]
        exact sq_eq_zero_iff.mp hb2
      have ha : g 0 0=0 := by nlinarith [sq_nonneg (g 0 1*Real.exp d)]
      rw [ha,hb] at hunit
      norm_num at hunit
    have heq := (eq_div_iff hdenom).mp hn
    have hz : (g 0 0 ^2-g 0 1 ^2)*(Real.exp d ^2-1)=0 := by nlinarith [heq]
    have hE : Real.exp d ^2-1 ≠ 0 := by
      intro h
      have hh : Real.exp d=1 := by nlinarith [Real.exp_pos d]
      apply hd
      apply Real.exp_injective
      simpa using hh
    have hsq := (mul_eq_zero.mp hz).resolve_right hE
    linarith
  have range_class (g : SL(2,ℝ)) (hgc : g 1 0 = -g 0 1) (hga : g 1 1 = g 0 0)
      (hsq : g 0 0 ^2 = g 0 1 ^2) :
      let R : SL(2,ℝ) := stabilizerRotation 1 1 (by norm_num)
      Set.range (fun t : ℝ => g • verticalPath t) =
        Set.range (fun t : ℝ => R • verticalPath t) := by
    let R : SL(2,ℝ) := stabilizerRotation 1 1 (by norm_num)
    change Set.range (fun t : ℝ => g • verticalPath t) = Set.range (fun t : ℝ => R • verticalPath t)
    let J : SL(2,ℝ) := ⟨!![0,-1;1,0],by simp [Matrix.det_fin_two]⟩
    have hJv (t : ℝ) : J • verticalPath t = verticalPath (-t) := by
      apply UpperHalfPlane.coe_injective
      rw [UpperHalfPlane.coe_specialLinearGroup_apply]
      simp [J,verticalPath,UpperHalfPlane.num,UpperHalfPlane.denom]
      apply Complex.ext
      · simp [Complex.div_re,Complex.normSq_apply]
      · simp [Complex.div_im,Complex.normSq_apply,Real.exp_neg]
        field_simp [Real.exp_ne_zero]
    have hRJ : R⁻¹=R*J := by
      apply Subtype.ext
      change (R⁻¹).val=(R*J).val
      simp only [Matrix.SpecialLinearGroup.coe_inv,Matrix.SpecialLinearGroup.coe_mul]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [R,J,stabilizerRotation,Matrix.SpecialLinearGroup.coe_inv,
          Matrix.adjugate_fin_two,Matrix.SpecialLinearGroup.coe_mul,
          Matrix.mul_apply,Fin.sum_univ_two] <;> ring
    have hneg (A : SL(2,ℝ)) (z : H2) : (-A) • z = A • z := by
      apply UpperHalfPlane.coe_injective
      rw [UpperHalfPlane.coe_specialLinearGroup_apply,UpperHalfPlane.coe_specialLinearGroup_apply]
      simp only [Matrix.SpecialLinearGroup.coe_neg,Matrix.neg_apply,
        Algebra.algebraMap_self,RingHom.id_apply,Complex.ofReal_neg,
        neg_mul,←neg_add]
      exact neg_div_neg_eq _ _
    have hRinv : Set.range (fun t : ℝ => R⁻¹ • verticalPath t) =
        Set.range (fun t : ℝ => R • verticalPath t) := by
      rw [hRJ]
      apply Set.Subset.antisymm
      · rintro _ ⟨t,rfl⟩
        refine ⟨-t,?_⟩
        change R • verticalPath (-t) = (R*J) • verticalPath t
        rw [mul_smul,hJv]
      · rintro _ ⟨t,rfl⟩
        refine ⟨-t,?_⟩
        change (R*J) • verticalPath (-t) = R • verticalPath t
        rw [mul_smul,hJv,neg_neg]
    have hdet : g 0 0*g 1 1-g 0 1*g 1 0=1 := by
      have h:=g.property
      change Matrix.det g.val=1 at h
      rw [Matrix.det_fin_two] at h
      exact h
    have hunit : g 0 0 ^2+g 0 1 ^2=1 := by rw [hgc,hga] at hdet;nlinarith [hdet]
    let p := 1/Real.sqrt 2
    have hp : 0 < Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
    have hp2 : Real.sqrt (2:ℝ)^2=2 := Real.sq_sqrt (by norm_num)
    have hpa2 : g 0 0 ^2=p^2 := by
      dsimp [p]
      field_simp [hp.ne']
      nlinarith [hunit,hsq,hp2]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hpa2 with ha | ha <;>
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hb | hb
    · have hg : g=R := by
        apply Subtype.ext
        change g.val = R.val
        ext i j
        fin_cases i <;> fin_cases j <;>
          norm_num [R,stabilizerRotation,hgc,hga,ha,←hb,p] <;> ring
      rw [hg]
    · have hg : g=R⁻¹ := by
        apply Subtype.ext
        change g.val = (R⁻¹).val
        simp only [Matrix.SpecialLinearGroup.coe_inv]
        ext i j
        have hbb : g 0 1 = -p := by linarith [ha,hb]
        fin_cases i <;> fin_cases j <;>
          norm_num [R,stabilizerRotation,Matrix.SpecialLinearGroup.coe_inv,
            Matrix.adjugate_fin_two,hgc,hga,ha,hbb,p] <;> ring
      rw [hg]
      exact hRinv
    · have hg : g= -R := by
        apply Subtype.ext
        change g.val = (-R).val
        simp only [Matrix.SpecialLinearGroup.coe_neg]
        ext i j
        fin_cases i <;> fin_cases j <;>
          norm_num [R,stabilizerRotation,Matrix.SpecialLinearGroup.coe_neg,hgc,hga,ha,←hb,p] <;> ring
      rw [hg]
      simp_rw [hneg]
    · have hg : g= -R⁻¹ := by
        apply Subtype.ext
        change g.val = (-R⁻¹).val
        simp only [Matrix.SpecialLinearGroup.coe_neg,Matrix.SpecialLinearGroup.coe_inv]
        ext i j
        have hbb : g 0 1 = p := by linarith [ha,hb]
        fin_cases i <;> fin_cases j <;>
          norm_num [R,stabilizerRotation,Matrix.SpecialLinearGroup.coe_inv,
            Matrix.adjugate_fin_two,Matrix.SpecialLinearGroup.coe_neg,hgc,hga,ha,hbb,p] <;> ring
      rw [hg]
      simp_rw [hneg]
      exact hRinv
  have Dadd (s t : ℝ) : D s*D t=D (s+t) := by
    apply Subtype.ext
    change (D s).val*(D t).val=(D (s+t)).val
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [D,Matrix.mul_apply,Fin.sum_univ_two,←Real.exp_add] <;>
      congr 1 <;> ring
  have Dzero : D 0=1 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [D]
  have Dv (s t : ℝ) : D s • verticalPath t=verticalPath (t+s) := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp [D,verticalPath,UpperHalfPlane.num,UpperHalfPlane.denom]
    rw [div_eq_mul_inv,←Complex.exp_neg]
    simp only [neg_neg]
    rw [mul_right_comm,←Complex.exp_add]
    rw [show (s:ℂ)/2+(s:ℂ)/2=(s:ℂ) by ring]
    apply Complex.ext <;> simp [Complex.exp_re,Complex.exp_im,Real.exp_add,mul_comm]
  have vzero : verticalPath 0=UpperHalfPlane.I := by
    apply UpperHalfPlane.ext_re_im <;> simp [verticalPath]
  have shift (r : ℝ) : Isometry (fun t : ℝ => r+t) := by
    refine Isometry.of_dist_eq ?_
    intro s t
    simp only [Real.dist_eq]
    congr 1
    ring
  have axis_range (f : ℝ → H2) (hf : Isometry f) (s₀ : ℝ)
      (e : H2 ≃ᵢ H2) (d : ℝ) (hd : d≠0)
      (he0 : e UpperHalfPlane.I=f s₀)
      (hmin : ∀ s,dist (f s₀) (e (verticalPath d)) ≤ dist (f s) (e (verticalPath d))) :
      Set.range f=Set.range (fun t : ℝ => e (R • verticalPath t)) := by
    let f' : ℝ → H2 := fun t => e.symm (f (s₀+t))
    have hf' : Isometry f' := e.symm.isometry.comp (hf.comp (shift s₀))
    obtain ⟨g,hg⟩ := normalize f' hf'
    have hge (t : ℝ) : e (g • verticalPath t)=f (s₀+t) := by
      rw [←hg]
      exact e.apply_symm_apply _
    have hgfix : g • UpperHalfPlane.I=UpperHalfPlane.I := by
      apply e.injective
      rw [←vzero,hge,add_zero,vzero,he0]
    have hgmin (t : ℝ) : dist (verticalPath d) UpperHalfPlane.I ≤
        dist (verticalPath d) (g • verticalPath t) := by
      have h0:=e.dist_eq (verticalPath d) UpperHalfPlane.I
      have ht:=e.dist_eq (verticalPath d) (g • verticalPath t)
      rw [he0] at h0
      rw [hge] at ht
      rw [←h0,←ht]
      simpa only [dist_comm] using hmin (s₀+t)
    have hsquare := orthogonal_square g d hd hgfix hgmin
    have hdet : g 0 0*g 1 1-g 0 1*g 1 0=1 := by
      have h:=g.property
      change Matrix.det g.val=1 at h
      rw [Matrix.det_fin_two] at h
      exact h
    have hden : ((g 1 0:ℂ)*Complex.I+g 1 1) ≠ 0 := by
      intro h
      have hr:=congrArg Complex.re h
      have hi:=congrArg Complex.im h
      simp at hr hi
      rw [hr,hi] at hdet
      norm_num at hdet
    have hcoeff := congrArg (fun z : H2 => (z:ℂ)) hgfix
    rw [UpperHalfPlane.coe_specialLinearGroup_apply] at hcoeff
    simp only [Algebra.algebraMap_self,RingHom.id_apply,UpperHalfPlane.coe_I] at hcoeff
    have hcross := (div_eq_iff hden).mp hcoeff
    have hre:=congrArg Complex.re hcross
    have him:=congrArg Complex.im hcross
    simp at hre him
    have hgc : g 1 0 = -g 0 1 := by linarith [hre]
    have hga : g 1 1 = g 0 0 := him.symm
    have hrg : Set.range (fun t : ℝ => g • verticalPath t)=Set.range (fun t : ℝ => R • verticalPath t) :=
      range_class g hgc hga hsquare
    apply Set.Subset.antisymm
    · rintro _ ⟨t,rfl⟩
      have hz : g • verticalPath (t-s₀) ∈ Set.range (fun u : ℝ => R • verticalPath u) :=
        hrg ▸ Set.mem_range_self (t-s₀)
      obtain ⟨u,hu⟩ := hz
      refine ⟨u,?_⟩
      change e (R • verticalPath u)=f t
      change R • verticalPath u = g • verticalPath (t-s₀) at hu
      rw [hu,hge]
      congr 1
      ring
    · rintro _ ⟨t,rfl⟩
      have hz : R • verticalPath t ∈ Set.range (fun u : ℝ => g • verticalPath u) :=
        hrg.symm ▸ Set.mem_range_self t
      obtain ⟨u,hu⟩ := hz
      refine ⟨s₀+u,?_⟩
      change f (s₀+u)=e (R • verticalPath t)
      change g • verticalPath u = R • verticalPath t at hu
      rw [←hu,hge]
  obtain ⟨s₀,t₀,hd,hminimum⟩ := minimum a b ha hb hsep
  let d := dist (a s₀) (b t₀)
  obtain ⟨g,hgp,hgq⟩ := align (a s₀) (b t₀) d hd rfl
  let e₀ : H2 ≃ᵢ H2 := IsometryEquiv.constSMul g
  let e₁ : H2 ≃ᵢ H2 := IsometryEquiv.constSMul (g*D d)
  have hep : e₀ UpperHalfPlane.I=a s₀ := hgp
  have heq : e₀ (verticalPath d)=b t₀ := hgq
  have he₁q : e₁ UpperHalfPlane.I=b t₀ := by
    change (g*D d) • UpperHalfPlane.I=b t₀
    rw [mul_smul,←vzero,Dv,zero_add]
    exact hgq
  have he₁p : e₁ (verticalPath (-d))=a s₀ := by
    change (g*D d) • verticalPath (-d)=a s₀
    rw [mul_smul,Dv,neg_add_cancel,vzero]
    exact hgp
  have hra := axis_range a ha s₀ e₀ d hd.ne' hep (by
    intro s
    rw [heq]
    exact hminimum s t₀)
  have hrb := axis_range b hb t₀ e₁ (-d) (neg_ne_zero.mpr hd.ne') he₁q (by
    intro t
    rw [he₁p]
    simpa only [dist_comm] using hminimum s₀ t)
  refine ⟨d,g*D (d/2),hd,?_,?_⟩
  · rw [hra]
    congr 1
    funext t
    change g • (R • verticalPath t) = (g*D (d/2)) • (D (-d/2) • (R • verticalPath t))
    have hprod : (g*D (d/2))*D (-d/2)=g := by
      rw [mul_assoc,Dadd,show d/2+(-d/2)=0 by ring,Dzero,mul_one]
    exact (congrArg (fun A : SL(2,ℝ) => A • (R • verticalPath t)) hprod).symm.trans
      (mul_smul _ _ _)
  · rw [hrb]
    congr 1
    funext t
    change (g*D d) • (R • verticalPath t) = (g*D (d/2)) • (D (d/2) • (R • verticalPath t))
    have hprod : (g*D (d/2))*D (d/2)=g*D d := by
      rw [mul_assoc,Dadd,show d/2+d/2=d by ring]
    exact (congrArg (fun A : SL(2,ℝ) => A • (R • verticalPath t)) hprod).symm.trans
      (mul_smul _ _ _)

theorem actual_positively_separated_complete_axes_simultaneous_sl_range_normalization
    (α β : ℝ → H2) (hα : Isometry α) (hβ : Isometry β)
    (hsep : ∃ ε : ℝ, 0 < ε ∧ ∀ s t : ℝ, ε ≤ dist (α s) (β t)) :
    let D : ℝ → SL(2,ℝ) := fun s =>
      ⟨!![Real.exp (s/2),0;0,Real.exp (-(s/2))],
        by simp [Matrix.det_fin_two, ←Real.exp_add]⟩
    let R : SL(2,ℝ) := stabilizerRotation 1 1 (by norm_num)
    ∃ d : ℝ, 0 < d ∧ ∃ g : SL(2,ℝ),
      (fun z : H2 => g • z) '' Set.range α =
        Set.range (fun t : ℝ => D (-d/2) • (R • verticalPath t)) ∧
      (fun z : H2 => g • z) '' Set.range β =
        Set.range (fun t : ℝ => D (d/2) • (R • verticalPath t)) := by
  dsimp only
  obtain ⟨d, u, hd, ha, hb⟩ :=
    axis_normalization_private_sl_normal_form α β hα hβ hsep
  refine ⟨d, hd, u⁻¹, ?_, ?_⟩
  · rw [ha]
    simp only [← Set.range_comp', Function.comp_def, inv_smul_smul]
  · rw [hb]
    simp only [← Set.range_comp', Function.comp_def, inv_smul_smul]

end CurveComplex.Hyperbolic
