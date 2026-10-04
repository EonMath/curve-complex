import CurveComplexGenusTwo.Hyperbolic.Stabilizer
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Calculus.ContDiff.Operations
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.RealSmoothMobiusCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.HyperbolicPlaneMobiusReuse

namespace CurveComplex.Hyperbolic
open scoped ContDiff
set_option maxHeartbeats 2000000

/-- Bounded smooth transition obligation for the actual induced metric atlas.
Real smoothness permits orientation-reversing hyperbolic isometries. -/
theorem real_smooth_hyperbolic_partial_isometry
    (e : OpenPartialHomeomorph H2 H2)
    (hmetric : ∀ x ∈ e.source, ∀ y ∈ e.source, dist (e x) (e y) = dist x y) :
    ContDiffOn ℝ ∞ (fun z : ℂ => ((e (UpperHalfPlane.ofComplex z) : H2) : ℂ))
      (((↑) : H2 → ℂ) '' e.source) := by
  have open_extension : ∀ (U : Set H2) (hU : IsOpen U) (hne : U.Nonempty)
      (f : U → H2) (hf : Isometry f), ∃ p : H2 ≃ᵢ H2, ∀ z : U, p z.val = f z := by
    intro U hU hne f hf
    have normalized_extension : ∀ (t r : ℝ) (ht : t ≠ 0) (hr : 0 < r)
      (U : Set H2) (hA : UpperHalfPlane.I ∈ U)
      (hB : (⟨⟨t,1⟩,by norm_num⟩ : H2) ∈ U) (hC : verticalPath r ∈ U)
      (f : U → H2) (hf : Isometry f),
      ∃ e : H2 ≃ᵢ H2, ∀ z : U, e z.val = f z := by
      intro t r ht hr U hA hB hC f hf
      classical
      have hyperbolic_reference_point_rigidity : ∀ (t s : ℝ) (ht : t ≠ 0) (hs : 0 < s) (hs1 : s ≠ 1)
        (z w : UpperHalfPlane)
        (hA : dist z UpperHalfPlane.I = dist w UpperHalfPlane.I)
        (hB : dist z (⟨⟨t,1⟩,by norm_num⟩ : UpperHalfPlane) =
          dist w (⟨⟨t,1⟩,by norm_num⟩ : UpperHalfPlane))
        (hC : dist z (⟨⟨0,s⟩,hs⟩ : UpperHalfPlane) =
          dist w (⟨⟨0,s⟩,hs⟩ : UpperHalfPlane)), z = w := by
        intro t s ht hs hs1 z w hA hB hC  
        have hz : z.im ≠ 0 := ne_of_gt z.im_pos
        have hw : w.im ≠ 0 := ne_of_gt w.im_pos
        have h1 := congrArg Real.cosh hA
        have h2 := congrArg Real.cosh hB
        have h3 := congrArg Real.cosh hC
        simp only [UpperHalfPlane.cosh_dist', UpperHalfPlane.I_re,
          UpperHalfPlane.I_im, sub_zero, one_pow, mul_one] at h1
        simp only [UpperHalfPlane.cosh_dist', UpperHalfPlane.mk_re,
          UpperHalfPlane.mk_im, one_pow, mul_one] at h2
        simp only [UpperHalfPlane.cosh_dist', UpperHalfPlane.mk_re,
          UpperHalfPlane.mk_im, sub_zero] at h3
        have H1 : (z.re ^ 2 + z.im ^ 2 + 1) * w.im =
            (w.re ^ 2 + w.im ^ 2 + 1) * z.im := by
          field_simp at h1
          nlinarith [h1]
        have H2 : ((z.re - t) ^ 2 + z.im ^ 2 + 1) * w.im =
            ((w.re - t) ^ 2 + w.im ^ 2 + 1) * z.im := by
          field_simp at h2
          nlinarith [h2]
        have H3 : (z.re ^ 2 + z.im ^ 2 + s ^ 2) * w.im =
            (w.re ^ 2 + w.im ^ 2 + s ^ 2) * z.im := by
          field_simp at h3
          nlinarith [h3]
        have hs2 : s ^ 2 - 1 ≠ 0 := by
          have hm : (s - 1) * (s + 1) ≠ 0 :=
            mul_ne_zero (sub_ne_zero.mpr hs1) (by linarith)
          intro h
          apply hm
          nlinarith [h]
        have hp : (s ^ 2 - 1) * (w.im - z.im) = 0 := by
          nlinarith [H1,H3]
        have him : z.im = w.im := by
          have he := (mul_eq_zero.mp hp).resolve_left hs2
          linarith
        have hp' : t * (z.re - w.re) * z.im = 0 := by
          rw [← him] at H1 H2
          nlinarith [H1,H2]
        have hre : z.re = w.re := by
          have he := (mul_eq_zero.mp hp').resolve_right hz
          have he' := (mul_eq_zero.mp he).resolve_left ht
          linarith
        apply UpperHalfPlane.ext
        exact Complex.ext hre him
      have normalize_at_arbitrary_radius : ∀ (r : ℝ) (hr : 0 < r) (z : H2)
        (h : dist UpperHalfPlane.I z = r),
        ∃ e : H2 ≃ᵢ H2, e UpperHalfPlane.I = UpperHalfPlane.I ∧
          e (verticalPath r) = z := by
        intro r hr z h  
        have hzero : verticalPath 0 = UpperHalfPlane.I := by
          apply UpperHalfPlane.ext_re_im <;> simp [verticalPath]
        have hstd : dist UpperHalfPlane.I (verticalPath r) = r := by
          rw [← hzero,verticalPath_isometry.dist_eq]
          simp [Real.dist_eq,abs_of_pos hr]
        have hsphere : Real.exp r * (z.re ^ 2 + z.im ^ 2 + 1) =
            z.im * (1 + (Real.exp r) ^ 2) := by
          have hc := congrArg Real.cosh (h.trans hstd.symm)
          rw [UpperHalfPlane.cosh_dist',UpperHalfPlane.cosh_dist'] at hc
          simp only [verticalPath,UpperHalfPlane.mk_re,UpperHalfPlane.mk_im,
            UpperHalfPlane.I_re,UpperHalfPlane.I_im,zero_sub,neg_sq,one_pow,
            zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hc
          field_simp at hc
          nlinarith [hc]
        let a : ℝ := 1 - Real.exp r * z.im
        let b : ℝ := z.re
        by_cases hpole : a = 0 ∧ b = 0
        · have him : z.im = Real.exp (-r) := by
            have he : Real.exp r ≠ 0 := (Real.exp_pos r).ne'
            have ha : Real.exp r * z.im = 1 := by dsimp [a] at hpole; linarith [hpole.1]
            rw [Real.exp_neg,← one_div]
            exact (eq_div_iff he).2 (by simpa [mul_comm] using ha)
          have hz : z = verticalPath (-r) := by
            apply UpperHalfPlane.ext_re_im
            · simpa [verticalPath,b] using hpole.2
            · simpa [verticalPath] using him
          refine ⟨IsometryEquiv.constSMul
            (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) ModularGroup.S),?_,?_⟩
          · rw [← hzero]
            change (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S • verticalPath 0 : H2) = verticalPath 0
            have hh := modular_S_verticalPath 0
            change (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S • verticalPath 0 : H2) = verticalPath (-0) at hh
            simpa only [neg_zero] using hh
          · rw [hz]
            change (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S • verticalPath r : H2) = verticalPath (-r)
            exact modular_S_verticalPath r
        · have hab : 0 < a ^ 2 + b ^ 2 := by
            by_contra hn
            have ha : a = 0 := by nlinarith [sq_nonneg a,sq_nonneg b]
            have hb : b = 0 := by nlinarith [sq_nonneg a,sq_nonneg b]
            exact hpole ⟨ha,hb⟩
          refine ⟨IsometryEquiv.constSMul (stabilizerRotation a b hab),
            stabilizerRotation_fixes_I a b hab,?_⟩
          change (stabilizerRotation a b hab • verticalPath r : H2) = z
          have hden (w : H2) : (-(b : ℂ) * (w : ℂ) + a) ≠ 0 := by
            intro he
            have him := congrArg Complex.im he
            simp [Complex.mul_im] at him
            have hb : b = 0 := by
              rcases him with hb | hw
              · exact hb
              · exact (w.im_pos.ne' hw).elim
            have ha : a ≠ 0 := by
              intro ha
              rw [ha,hb] at hab
              norm_num at hab
            exact ha (by simpa [hb] using he)
          have hEim : (Complex.exp (r : ℂ)).im = 0 := Complex.exp_ofReal_im r
          have hEre : (Complex.exp (r : ℂ)).re = Real.exp r := Complex.exp_ofReal_re r
          apply UpperHalfPlane.coe_injective
          rw [stabilizerRotation_coe_smul]
          apply (div_eq_iff (hden (verticalPath r))).2
          apply Complex.ext
          · simp [verticalPath,Complex.add_re,Complex.mul_re,Complex.neg_re,
              Complex.mul_im,Complex.neg_im]
            dsimp [a,b]
            ring
          · simp [verticalPath,Complex.add_im,Complex.mul_im,Complex.neg_im,
              Complex.mul_re,Complex.neg_re]
            dsimp [a,b]
            nlinarith [hsphere]
      have ordered_pair_at_arbitrary_distance (r : ℝ) (hr : 0 < r)
          (a b : H2) (hd : dist a b = r) :
          ∃ e : H2 ≃ᵢ H2, e UpperHalfPlane.I = a ∧ e (verticalPath r) = b := by
        let e₀ : H2 ≃ᵢ H2 := IsometryEquiv.constSMul a.toSL2R
        have h₀ : e₀ UpperHalfPlane.I = a := a.toSL2R_smul_I
        let w : H2 := e₀.symm b
        have hw : dist UpperHalfPlane.I w = r := by
          have he := e₀.dist_eq UpperHalfPlane.I (e₀.symm b)
          rw [e₀.apply_symm_apply,h₀] at he
          exact he.symm.trans hd
        obtain ⟨q,hqI,hqr⟩ := normalize_at_arbitrary_radius r hr w hw
        refine ⟨q.trans e₀,?_,?_⟩
        · rw [IsometryEquiv.trans_apply,hqI,h₀]
        · rw [IsometryEquiv.trans_apply,hqr]
          exact e₀.apply_symm_apply b
      have two_reference_ambiguity (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1)
          (z w : H2)
          (hA : dist z UpperHalfPlane.I = dist w UpperHalfPlane.I)
          (hC : dist z (⟨⟨0,s⟩,hs⟩ : H2) = dist w (⟨⟨0,s⟩,hs⟩ : H2)) :
          z.im = w.im ∧ (z.re = w.re ∨ z.re = -w.re) := by
        have hz : z.im ≠ 0 := ne_of_gt z.im_pos
        have hw : w.im ≠ 0 := ne_of_gt w.im_pos
        have h1 := congrArg Real.cosh hA
        have h3 := congrArg Real.cosh hC
        simp only [UpperHalfPlane.cosh_dist', UpperHalfPlane.I_re,
          UpperHalfPlane.I_im, sub_zero, one_pow, mul_one] at h1
        simp only [UpperHalfPlane.cosh_dist', UpperHalfPlane.mk_re,
          UpperHalfPlane.mk_im, sub_zero] at h3
        have H1 : (z.re ^ 2 + z.im ^ 2 + 1) * w.im =
            (w.re ^ 2 + w.im ^ 2 + 1) * z.im := by
          field_simp at h1
          nlinarith [h1]
        have H3 : (z.re ^ 2 + z.im ^ 2 + s ^ 2) * w.im =
            (w.re ^ 2 + w.im ^ 2 + s ^ 2) * z.im := by
          field_simp at h3
          nlinarith [h3]
        have hs2 : s ^ 2 - 1 ≠ 0 := by
          have hm : (s - 1) * (s + 1) ≠ 0 :=
            mul_ne_zero (sub_ne_zero.mpr hs1) (by linarith)
          intro h
          apply hm
          nlinarith [h]
        have hp : (s ^ 2 - 1) * (w.im - z.im) = 0 := by
          nlinarith [H1,H3]
        have him : z.im = w.im := by
          have he := (mul_eq_zero.mp hp).resolve_left hs2
          linarith
        have hsq : z.re ^ 2 = w.re ^ 2 := by
          rw [← him] at H1
          have he : (z.re ^ 2 - w.re ^ 2) * z.im = 0 := by nlinarith [H1]
          have he' := (mul_eq_zero.mp he).resolve_right hz
          linarith
        exact ⟨him,sq_eq_sq_iff_eq_or_eq_neg.mp hsq⟩
      let R : H2 ≃ᵢ H2 := {
        toFun := fun z => ⟨⟨-z.re,z.im⟩,z.im_pos⟩
        invFun := fun z => ⟨⟨-z.re,z.im⟩,z.im_pos⟩
        left_inv := by intro z; apply UpperHalfPlane.ext_re_im <;> simp
        right_inv := by intro z; apply UpperHalfPlane.ext_re_im <;> simp
        isometry_toFun := Isometry.of_dist_eq (by
          intro z w
          apply Real.cosh_strictMonoOn.injOn (dist_nonneg) (dist_nonneg)
          rw [UpperHalfPlane.cosh_dist',UpperHalfPlane.cosh_dist']
          simp only [UpperHalfPlane.mk_re,UpperHalfPlane.mk_im]
          congr 1
          ring) }
      have hRI : R UpperHalfPlane.I = UpperHalfPlane.I := by
        apply UpperHalfPlane.ext_re_im <;> simp [R]
      have hRC : R (verticalPath r) = verticalPath r := by
        apply UpperHalfPlane.ext_re_im <;> simp [R,verticalPath]
      let A : U := ⟨UpperHalfPlane.I,hA⟩
      let B : U := ⟨⟨⟨t,1⟩,by norm_num⟩,hB⟩
      let C : U := ⟨verticalPath r,hC⟩
      have hdAC : dist (f A) (f C) = r := by
        rw [hf.dist_eq]
        change dist UpperHalfPlane.I (verticalPath r) = r
        have hzero : verticalPath 0 = UpperHalfPlane.I := by
          apply UpperHalfPlane.ext_re_im <;> simp [verticalPath]
        rw [← hzero,verticalPath_isometry.dist_eq]
        simp [Real.dist_eq,abs_of_pos hr]
      obtain ⟨e₀,h₀A,h₀C⟩ := ordered_pair_at_arbitrary_distance r hr (f A) (f C) hdAC
      let g : U → H2 := fun z => e₀.symm (f z)
      have hg : Isometry g := e₀.symm.isometry.comp hf
      have hgA : g A = UpperHalfPlane.I := by
        dsimp [g]
        rw [← h₀A,e₀.symm_apply_apply]
      have hgC : g C = verticalPath r := by
        dsimp [g]
        rw [← h₀C,e₀.symm_apply_apply]
      have hBA : dist (g B) UpperHalfPlane.I = dist B.val UpperHalfPlane.I := by
        have hh := hg.dist_eq B A
        simpa only [hgA,Subtype.dist_eq,A] using hh
      have hBC : dist (g B) (verticalPath r) = dist B.val (verticalPath r) := by
        have hh := hg.dist_eq B C
        simpa only [hgC,Subtype.dist_eq,C] using hh
      have hs1 : Real.exp r ≠ 1 := by
        intro he
        have he' : r = 0 := Real.exp_injective (show Real.exp r = Real.exp 0 by simpa using he)
        linarith
      obtain ⟨him,hre⟩ := two_reference_ambiguity (Real.exp r) (Real.exp_pos r) hs1
        (g B) B.val hBA hBC
      have hBnormal : g B = B.val ∨ R (g B) = B.val := by
        rcases hre with hp | hn
        · left
          exact UpperHalfPlane.ext_re_im hp him
        · right
          apply UpperHalfPlane.ext_re_im
          · change -(g B).re = t
            change (g B).re = -t at hn
            linarith
          · exact him
      obtain ⟨q,hqA,hqB,hqC⟩ : ∃ q : H2 ≃ᵢ H2,
          q UpperHalfPlane.I = UpperHalfPlane.I ∧ q (g B) = B.val ∧
            q (verticalPath r) = verticalPath r := by
        rcases hBnormal with hp | hn
        · exact ⟨IsometryEquiv.refl _,rfl,hp,rfl⟩
        · exact ⟨R,hRI,hn,hRC⟩
      have hall (z : U) : q (g z) = z.val := by
        refine hyperbolic_reference_point_rigidity t (Real.exp r) ht (Real.exp_pos r) hs1 (q (g z)) z.val ?_ ?_ ?_
        · have hh := (q.isometry.comp hg).dist_eq z A
          simpa only [Function.comp_apply,hgA,hqA,Subtype.dist_eq,A] using hh
        · have hh := (q.isometry.comp hg).dist_eq z B
          simpa only [Function.comp_apply,hqB,Subtype.dist_eq] using hh
        · have hh := (q.isometry.comp hg).dist_eq z C
          change dist (q (g z)) (q (g C)) = dist z.val C.val at hh
          rw [hgC,hqC] at hh
          change dist (q (g z)) (verticalPath r) = dist z.val (verticalPath r) at hh
          simpa only [verticalPath] using hh
      refine ⟨q.symm.trans e₀,?_⟩
      intro z
      rw [IsometryEquiv.trans_apply,← hall z,q.symm_apply_apply]
      exact e₀.apply_symm_apply (f z)
    obtain ⟨p,hp⟩ := hne
    let a : H2 ≃ᵢ H2 := IsometryEquiv.constSMul p.toSL2R
    have ha : a UpperHalfPlane.I = p := p.toSL2R_smul_I
    let V : Set H2 := a ⁻¹' U
    have hV : IsOpen V := hU.preimage a.continuous
    have hIV : UpperHalfPlane.I ∈ V := by change a UpperHalfPlane.I ∈ U; rw [ha]; exact hp
    let horizontal : ℝ → H2 := fun t => ⟨⟨t,1⟩,by norm_num⟩
    have hhor : Continuous horizontal := by
      apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
      have hh : Continuous (fun t : ℝ => (t : ℂ) + Complex.I) :=
        Complex.continuous_ofReal.add continuous_const
      convert hh using 1
      ext t <;> simp [horizontal,Complex.ext_iff]
    have hhor0 : horizontal 0 = UpperHalfPlane.I := by
      apply UpperHalfPlane.ext_re_im <;> simp [horizontal]
    have hvert0 : verticalPath 0 = UpperHalfPlane.I := by
      apply UpperHalfPlane.ext_re_im <;> simp [verticalPath]
    let W : Set ℝ := horizontal ⁻¹' V ∩ verticalPath ⁻¹' V
    have hW : IsOpen W :=
      (hV.preimage hhor).inter (hV.preimage verticalPath_isometry.continuous)
    have h0W : (0 : ℝ) ∈ W := by
      exact ⟨by change horizontal 0 ∈ V; rw [hhor0]; exact hIV,
        by change verticalPath 0 ∈ V; rw [hvert0]; exact hIV⟩
    obtain ⟨δ,hδ,hδW⟩ := Metric.isOpen_iff.mp hW 0 h0W
    let r := δ / 2
    have hr : 0 < r := by dsimp [r]; linarith
    have hrW : r ∈ W := hδW (by
      rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hr]
      dsimp [r]
      linarith)
    let F : V → H2 := fun z => f ⟨a z.val,z.property⟩
    have hF : Isometry F := Isometry.of_dist_eq (by
      intro z w
      calc
        dist (F z) (F w) = dist (a z.val) (a w.val) := hf.dist_eq _ _
        _ = dist z w := a.dist_eq _ _)
    obtain ⟨e,he⟩ := normalized_extension r r hr.ne' hr V hIV hrW.1 hrW.2 F hF
    refine ⟨a.symm.trans e,?_⟩
    intro z
    let y : V := ⟨a.symm z.val,by
      change a (a.symm z.val) ∈ U
      rw [a.apply_symm_apply]
      exact z.property⟩
    change e y.val = f z
    rw [he y]
    change f ⟨a (a.symm z.val),_⟩ = f z
    congr 1
    apply Subtype.ext
    exact a.apply_symm_apply z.val
  by_cases hne : e.source.Nonempty
  · let f : e.source → H2 := fun z => e z
    have hf : Isometry f := Isometry.of_dist_eq (fun z w => hmetric z z.property w w.property)
    obtain ⟨p, hp⟩ := open_extension e.source e.open_source hne f hf
    obtain ⟨g, hg⟩ := axis_metric_isometry_gl_representation p
    have hs : ((↑) : H2 → ℂ) '' e.source ⊆ {z : ℂ | 0 < z.im} := by
      rintro z ⟨y, hy, rfl⟩
      exact y.im_pos
    apply ((real_smooth_gl_upper_half_plane_action g).mono hs).congr
    rintro z ⟨y, hy, rfl⟩
    simpa only [UpperHalfPlane.ofComplex_apply, f] using
      congrArg (fun w : H2 => (w : ℂ)) ((hp ⟨y, hy⟩).symm.trans (hg y))
  · have hs : e.source = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp [hs]


end CurveComplex.Hyperbolic
