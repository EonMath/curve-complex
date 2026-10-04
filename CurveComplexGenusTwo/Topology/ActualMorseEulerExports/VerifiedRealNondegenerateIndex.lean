import Mathlib.Analysis.Calculus.FDeriv.Basic
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualCircleSourceWindingTransport
import CurveComplexGenusTwo.Hyperbolic.ActualHaasBoundary.HaasActualCircleMapWindingHomotopySourceReviewRequest
open scoped unitInterval
open Set Topology
set_option backward.isDefEq.respectTransparency false
private theorem actual_circle_power_homotopy_exponent_unique (m n : ℤ)
    (h : (⟨fun z : Circle => z ^ m, continuous_zpow m⟩ : C(Circle,Circle)).Homotopic
      ⟨fun z : Circle => z ^ n, continuous_zpow n⟩) : m = n := by
  obtain ⟨H⟩ := h
  let G : C(CurveComplex.Interval × ℝ,Circle) :=
    ⟨fun tx => H (tx.1,Circle.exp tx.2), by fun_prop⟩
  let F : C(ℝ,ℝ) := ⟨fun x => (m : ℝ)*x, by fun_prop⟩
  have hzero (x : ℝ) : G (0,x) = Circle.exp (F x) := by
    change H (0,Circle.exp x) = Circle.exp ((m : ℝ)*x)
    rw [H.apply_zero]
    simpa only [zsmul_eq_mul,ContinuousMap.coe_mk] using (Circle.exp_zsmul x m).symm
  have hGperiod (t : CurveComplex.Interval) (k : ℤ) (x : ℝ) :
      G (t,x+(k:ℝ)*(2*Real.pi)) = G (t,x) := by
    dsimp only [G,ContinuousMap.coe_mk]
    rw [Circle.exp_add, Circle.exp_int_mul_two_pi, mul_one]
  have hFperiod (k : ℤ) (x : ℝ) :
      F (x+(k:ℝ)*(2*Real.pi)) = F x+((k*m:ℤ):ℝ)*(2*Real.pi) := by
    simp only [F,ContinuousMap.coe_mk,Int.cast_mul]
    ring
  obtain ⟨A,hAlift,hA0,hAperiod⟩ :=
    actual_circle_source_homotopy_retains_integer_winding G F m hzero hGperiod hFperiod
  have hA1 (x : ℝ) : Circle.exp (A (1,x)) = (Circle.exp x)^n := by
    exact (hAlift 1 x).trans (H.apply_one (Circle.exp x))
  have hA10 : Circle.exp (A (1,0)) = 1 := by simpa using hA1 0
  have heq : (fun x : ℝ => A (1,x)) = (fun x : ℝ => (n:ℝ)*x + A (1,0)) := by
    apply Circle.isCoveringMap_exp.eq_of_comp_eq
      (A.continuous.comp (continuous_const.prodMk continuous_id))
      (by fun_prop) ?_ 0 (by simp)
    funext x
    change Circle.exp (A (1,x)) = Circle.exp ((n:ℝ)*x + A (1,0))
    rw [hA1, Circle.exp_add, hA10, mul_one]
    simpa only [zsmul_eq_mul,ContinuousMap.coe_mk] using (Circle.exp_zsmul x n).symm
  have hp := hAperiod 1 1 0
  rw [congrFun heq _,congrFun heq _] at hp
  have hm : (m:ℝ)*(2*Real.pi) = (n:ℝ)*(2*Real.pi) := by
    simpa only [zero_add,Int.cast_one,one_mul,mul_zero,zero_add] using
      (add_right_cancel (show (n:ℝ)*(2*Real.pi)+A (1,0) =
        (m:ℝ)*(2*Real.pi)+A (1,0) by simpa [add_comm] using hp)).symm
  exact_mod_cast mul_right_cancel₀ (mul_ne_zero (by norm_num) Real.pi_ne_zero) hm

private noncomputable def actualCircleMapDegree (f : C(Circle,Circle)) : ℤ :=
  Classical.choose (actual_circle_map_winding_homotopy_source f)

private theorem actual_circle_map_degree_of_power_homotopy (f : C(Circle,Circle)) (n : ℤ)
    (h : f.Homotopic ⟨fun z : Circle => z^n,continuous_zpow n⟩) : actualCircleMapDegree f = n := by
  have hd : f.Homotopic ⟨fun z : Circle => z^(actualCircleMapDegree f),continuous_zpow _⟩ :=
    Classical.choose_spec (actual_circle_map_winding_homotopy_source f)
  exact actual_circle_power_homotopy_exponent_unique _ _ (hd.symm.trans h)

private theorem actual_circle_map_degree_homotopy_invariant (f g : C(Circle,Circle))
    (h : f.Homotopic g) : actualCircleMapDegree f = actualCircleMapDegree g := by
  apply actual_circle_map_degree_of_power_homotopy
  exact h.trans (Classical.choose_spec (actual_circle_map_winding_homotopy_source g))

private noncomputable def actualNormalize (w : ℂ) (hw : w ≠ 0) : Circle :=
  ⟨w / (‖w‖ : ℂ), by
    apply mem_sphere_zero_iff_norm.mpr
    simp [norm_ne_zero_iff.mpr hw]⟩

private theorem actualNormalize_coe (w : ℂ) (hw : w ≠ 0) :
    (actualNormalize w hw : ℂ) = w / (‖w‖ : ℂ) := rfl

private theorem actualNormalize_continuous {X : Type*} [TopologicalSpace X]
    (F : C(X, ℂ)) (hF : ∀ x, F x ≠ 0) :
    Continuous (fun x => actualNormalize (F x) (hF x)) := by
  apply Continuous.subtype_mk
  have hdiv : Continuous (fun x => F x / (‖F x‖ : ℂ)) := by
    have hc : Continuous (fun x => (‖F x‖ : ℂ)) := by fun_prop
    have hn : ∀ x, (‖F x‖ : ℂ) ≠ 0 := by
      intro x
      exact_mod_cast norm_ne_zero_iff.mpr (hF x)
    convert F.continuous.div hc hn using 1
  simpa only [actualNormalize_coe] using hdiv

private theorem actualNormalize_homotopic {f₀ f₁ : C(Circle,Circle)}
    (F : C(CurveComplex.Interval × Circle, ℂ))
    (hF : ∀ x, F x ≠ 0)
    (h₀ : ∀ z, (f₀ z : ℂ) = F (0,z) / (‖F (0,z)‖ : ℂ))
    (h₁ : ∀ z, (f₁ z : ℂ) = F (1,z) / (‖F (1,z)‖ : ℂ)) :
    f₀.Homotopic f₁ := by
  refine ⟨{
    toFun := fun x => actualNormalize (F x) (hF x)
    continuous_toFun := actualNormalize_continuous F hF
    map_zero_left := ?_
    map_one_left := ?_ }⟩
  · intro z
    apply Circle.coe_injective
    exact (h₀ z).symm
  · intro z
    apply Circle.coe_injective
    exact (h₁ z).symm

private theorem actual_segment_nonzero (a b : ℂ)
    (h : ‖b - a‖ < ‖a‖) (s : ℝ) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
    a + (s : ℂ) * (b - a) ≠ 0 := by
  intro hzero
  have ha : a = -(s : ℂ) * (b - a) := by
    calc
      a = -((s : ℂ) * (b - a)) := eq_neg_of_add_eq_zero_left hzero
      _ = -(s : ℂ) * (b - a) := by ring
  have hnorm : ‖a‖ = s * ‖b - a‖ := by
    calc
      ‖a‖ = ‖-((s : ℂ) * (b - a))‖ := congrArg norm (by simpa only [neg_mul] using ha)
      _ = s * ‖b - a‖ := by simp [Complex.norm_real, abs_of_nonneg hs₀]
  have hle : s * ‖b - a‖ ≤ ‖b - a‖ := by
    simpa using mul_le_mul_of_nonneg_right hs₁ (norm_nonneg (b - a))
  exact (not_lt_of_ge (hnorm.trans_le hle)) h

private theorem actual_real_linear_dominates_error
    (g : C(ℂ,ℂ)) (A : ℂ ≃L[ℝ] ℂ)
    (hg0 : g 0 = 0) (hderiv : HasFDerivAt g A.toContinuousLinearMap 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ x : ℂ, x ≠ 0 → ‖x‖ < r → ‖g x - A x‖ < ‖A x‖ := by
  let M : ℝ := ‖(A.symm : ℂ →L[ℝ] ℂ)‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hε : 0 < (1 / M : ℝ) := by positivity
  have hlittle : (fun x : ℂ => g x - A x) =o[𝓝 0] (fun x => x) := by
    simpa [hasFDerivAt_iff_isLittleO_nhds_zero, hg0] using hderiv.isLittleO
  obtain ⟨r, hr, hbound⟩ := Metric.eventually_nhds_iff_ball.mp
    (Asymptotics.IsLittleO.bound hlittle hε)
  refine ⟨r, hr, ?_⟩
  intro x hx hxr
  have hAx : A x ≠ 0 := by simpa using A.injective.ne hx
  have hAxpos : 0 < ‖A x‖ := norm_pos_iff.mpr hAx
  have hxnorm : ‖x‖ ≤ ‖(A.symm : ℂ →L[ℝ] ℂ)‖ * ‖A x‖ := by
    simpa using (A.symm : ℂ →L[ℝ] ℂ).le_opNorm (A x)
  have he : ‖g x - A x‖ ≤ (1 / M) * ‖x‖ := by
    apply hbound
    simpa [Metric.mem_ball, dist_eq_norm] using hxr
  have hstrict : (1 / M) * (‖(A.symm : ℂ →L[ℝ] ℂ)‖ * ‖A x‖) < ‖A x‖ := by
    have hquot : ‖(A.symm : ℂ →L[ℝ] ℂ)‖ / M < 1 :=
      (div_lt_iff₀ hM).2 (by dsimp [M]; linarith)
    calc
      (1 / M) * (‖(A.symm : ℂ →L[ℝ] ℂ)‖ * ‖A x‖) =
          (‖(A.symm : ℂ →L[ℝ] ℂ)‖ / M) * ‖A x‖ := by ring
      _ < 1 * ‖A x‖ := mul_lt_mul_of_pos_right hquot hAxpos
      _ = ‖A x‖ := one_mul _
  exact he.trans_lt ((mul_le_mul_of_nonneg_left hxnorm (by positivity)).trans_lt hstrict)

private theorem actual_boundary_homotopic_linear
    (g : C(ℂ,ℂ)) (A : ℂ ≃L[ℝ] ℂ) (ρ : ℝ)
    (hρ : 0 < ρ)
    (herror : ∀ z : Circle,
      ‖g ((ρ : ℂ) * z) - A ((ρ : ℂ) * z)‖ < ‖A ((ρ : ℂ) * z)‖)
    (f : C(Circle,Circle))
    (hf : ∀ z, (f z : ℂ) = g ((ρ : ℂ) * z) / (‖g ((ρ : ℂ) * z)‖ : ℂ)) :
    ∃ m : C(Circle,Circle),
      (∀ z, (m z : ℂ) =
        A ((ρ : ℂ) * z) / (‖A ((ρ : ℂ) * z)‖ : ℂ)) ∧ f.Homotopic m := by
  have hx (z : Circle) : (ρ : ℂ) * (z : ℂ) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast ne_of_gt hρ) z.coe_ne_zero
  have hA (z : Circle) : A ((ρ : ℂ) * z) ≠ 0 := by
    simpa using A.injective.ne (hx z)
  let L : C(Circle,ℂ) := ⟨fun z => A ((ρ : ℂ) * z), by fun_prop⟩
  let m : C(Circle,Circle) :=
    ⟨fun z => actualNormalize (L z) (hA z), actualNormalize_continuous L hA⟩
  let F : C(CurveComplex.Interval × Circle,ℂ) :=
    ⟨fun tz => A ((ρ : ℂ) * tz.2) +
       ((1 - (tz.1 : ℝ) : ℝ) : ℂ) *
         (g ((ρ : ℂ) * tz.2) - A ((ρ : ℂ) * tz.2)), by fun_prop⟩
  have hF (tz : CurveComplex.Interval × Circle) : F tz ≠ 0 := by
    have ht := tz.1.property
    have hs₀ : 0 ≤ 1 - (tz.1 : ℝ) := sub_nonneg.mpr ht.2
    have hs₁ : 1 - (tz.1 : ℝ) ≤ 1 := by linarith [ht.1]
    exact actual_segment_nonzero _ _ (herror tz.2) _ hs₀ hs₁
  refine ⟨m, ?_, ?_⟩
  · intro z
    simpa [m, L] using actualNormalize_coe (A ((ρ : ℂ) * z)) (hA z)
  · apply actualNormalize_homotopic F hF
    · intro z
      have hz : F (0,z) = g ((ρ : ℂ) * z) := by simp [F]
      rw [hz]
      exact hf z
    · intro z
      have hz : F (1,z) = A ((ρ : ℂ) * z) := by simp [F]
      rw [hz]
      simp [m, L, actualNormalize_coe]

private theorem actual_real_linear_apply (A : ℂ ≃L[ℝ] ℂ) (z : ℂ) :
    A z = (z.re : ℂ) * A 1 + (z.im : ℂ) * A Complex.I := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [map_add]
  have hr : A (z.re : ℂ) = (z.re : ℂ) * A 1 := by
    simpa [smul_eq_mul] using (A.map_smul z.re (1 : ℂ))
  have hi : A ((z.im : ℂ) * Complex.I) = (z.im : ℂ) * A Complex.I := by
    simpa [smul_eq_mul] using (A.map_smul z.im Complex.I)
  rw [hr, hi]

private theorem actual_real_linear_det_formula (A : ℂ ≃L[ℝ] ℂ) :
    LinearMap.det (A.toLinearEquiv.toLinearMap : ℂ →ₗ[ℝ] ℂ) =
      (A 1).re * (A Complex.I).im - (A Complex.I).re * (A 1).im := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr, Complex.coe_basisOneI]

private theorem actual_real_linear_det_ne_zero (A : ℂ ≃L[ℝ] ℂ) :
    (A 1).re * (A Complex.I).im - (A Complex.I).re * (A 1).im ≠ 0 := by
  rw [← actual_real_linear_det_formula]
  intro h
  have hker := LinearMap.bot_lt_ker_of_det_eq_zero h
  have hinj : Function.Injective (A.toLinearEquiv.toLinearMap : ℂ →ₗ[ℝ] ℂ) := A.injective
  exact (not_lt_of_ge bot_le) (hker.trans_le (LinearMap.ker_eq_bot.mpr hinj).le)

private theorem actual_real_combo_ne_zero (c d : ℂ)
    (hdet : c.re * d.im - d.re * c.im ≠ 0) (z : ℂ) (hz : z ≠ 0) :
    (z.re : ℂ) * c + (z.im : ℂ) * d ≠ 0 := by
  intro hzero
  have hre : z.re * c.re + z.im * d.re = 0 := by
    have h := congrArg Complex.re hzero
    simpa [Complex.add_re, Complex.mul_re] using h
  have him : z.re * c.im + z.im * d.im = 0 := by
    have h := congrArg Complex.im hzero
    simpa [Complex.add_im, Complex.mul_im] using h
  have hxdet : z.re * (c.re * d.im - d.re * c.im) = 0 := by
    linear_combination d.im * hre - d.re * him
  have hx : z.re = 0 := (mul_eq_zero.mp hxdet).resolve_right hdet
  have hydet : z.im * (c.re * d.im - d.re * c.im) = 0 := by
    linear_combination c.re * him - c.im * hre
  have hy : z.im = 0 := (mul_eq_zero.mp hydet).resolve_right hdet
  have hzeroz : z = 0 := by
    apply Complex.ext <;> simp [hx, hy]
  exact hz hzeroz

private theorem actual_circle_mul_power_homotopic (u : Circle) (n : ℤ) :
    (⟨fun z : Circle => u * z ^ n, by fun_prop⟩ : C(Circle,Circle)).Homotopic
      ⟨fun z : Circle => z ^ n, continuous_zpow n⟩ := by
  obtain ⟨θ, hθ⟩ := Circle.exp_surjective u
  refine ⟨{
    toFun := fun tz => Circle.exp ((1 - (tz.1 : ℝ)) * θ) * tz.2 ^ n
    continuous_toFun := by fun_prop
    map_zero_left := ?_
    map_one_left := ?_ }⟩
  · intro z
    simpa using congrArg (fun a : Circle => a * z ^ n) hθ
  · intro z
    simp

private theorem actual_det_interp (c d e : ℂ) (t : ℝ) :
    c.re * (((1 - t : ℝ) : ℂ) * d + (t : ℂ) * e).im -
      (((1 - t : ℝ) : ℂ) * d + (t : ℂ) * e).re * c.im =
    (1 - t) * (c.re * d.im - d.re * c.im) +
      t * (c.re * e.im - e.re * c.im) := by
  simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  ring

private theorem actual_det_mul_I (c : ℂ) :
    c.re * (c * Complex.I).im - (c * Complex.I).re * c.im = ‖c‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]

private theorem actual_det_neg_mul_I (c : ℂ) :
    c.re * (-c * Complex.I).im - (-c * Complex.I).re * c.im = -(‖c‖ ^ 2) := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

private theorem actual_real_combo_homotopic (c d e : ℂ)
    (hdet : ∀ t : CurveComplex.Interval,
      c.re * (((1 - (t : ℝ) : ℝ) : ℂ) * d + (t : ℂ) * e).im -
        (((1 - (t : ℝ) : ℝ) : ℂ) * d + (t : ℂ) * e).re * c.im ≠ 0)
    (f : C(Circle,Circle))
    (hf : ∀ z, (f z : ℂ) =
      (((z : ℂ).re : ℂ) * c + ((z : ℂ).im : ℂ) * d) /
        (‖((z : ℂ).re : ℂ) * c + ((z : ℂ).im : ℂ) * d‖ : ℂ)) :
    ∃ m : C(Circle,Circle),
      (∀ z, (m z : ℂ) =
        (((z : ℂ).re : ℂ) * c + ((z : ℂ).im : ℂ) * e) /
          (‖((z : ℂ).re : ℂ) * c + ((z : ℂ).im : ℂ) * e‖ : ℂ)) ∧
      f.Homotopic m := by
  let F : C(CurveComplex.Interval × Circle, ℂ) :=
    ⟨fun tz => (((tz.2 : ℂ).re : ℂ) * c + ((tz.2 : ℂ).im : ℂ) *
      (((1 - (tz.1 : ℝ) : ℝ) : ℂ) * d + (tz.1 : ℂ) * e)), by fun_prop⟩
  have hF (tz : CurveComplex.Interval × Circle) : F tz ≠ 0 := by
    exact actual_real_combo_ne_zero c _ (hdet tz.1) _ tz.2.coe_ne_zero
  have he (z : Circle) :
      (((z : ℂ).re : ℂ) * c + ((z : ℂ).im : ℂ) * e) ≠ 0 := by
    simpa [F] using hF (1,z)
  let L : C(Circle,ℂ) :=
    ⟨fun z => (((z : ℂ).re : ℂ) * c + ((z : ℂ).im : ℂ) * e), by fun_prop⟩
  let m : C(Circle,Circle) :=
    ⟨fun z => actualNormalize (L z) (he z), actualNormalize_continuous L he⟩
  refine ⟨m, ?_, ?_⟩
  · intro z
    simpa [m, L] using actualNormalize_coe _ (he z)
  · apply actualNormalize_homotopic F hF
    · intro z
      have hz : F (0,z) = (((z : ℂ).re : ℂ) * c + ((z : ℂ).im : ℂ) * d) := by
        simp [F]
      rw [hz]
      exact hf z
    · intro z
      have hz : F (1,z) = (((z : ℂ).re : ℂ) * c + ((z : ℂ).im : ℂ) * e) := by
        simp [F]
      rw [hz]
      simp [m, L, actualNormalize_coe]

private theorem actual_normalized_pos_smul (ρ : ℝ) (hρ : 0 < ρ) (w : ℂ) :
    ((ρ : ℂ) * w) / (‖(ρ : ℂ) * w‖ : ℂ) = w / (‖w‖ : ℂ) := by
  have hρ₀ : (ρ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hρ
  rw [norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
  push_cast
  exact mul_div_mul_left w (‖w‖ : ℂ) hρ₀

private theorem actual_real_combo_positive_degree (c : ℂ) (hc : c ≠ 0)
    (m : C(Circle,Circle))
    (hm : ∀ z, (m z : ℂ) =
      (((z : ℂ).re : ℂ) * c + ((z : ℂ).im : ℂ) * (c * Complex.I)) /
        (‖(((z : ℂ).re : ℂ) * c + ((z : ℂ).im : ℂ) * (c * Complex.I))‖ : ℂ)) :
    actualCircleMapDegree m = 1 := by
  let u : Circle := actualNormalize c hc
  have heq (z : Circle) : m z = u * z := by
    apply Circle.coe_injective
    rw [hm z, Circle.coe_mul, actualNormalize_coe]
    have hlin : (((z : ℂ).re : ℂ) * c + ((z : ℂ).im : ℂ) * (c * Complex.I)) =
        c * (z : ℂ) := by
      calc
        _ = c * (((z : ℂ).re : ℂ) + ((z : ℂ).im : ℂ) * Complex.I) := by ring
        _ = c * (z : ℂ) := by rw [Complex.re_add_im]
    rw [hlin, norm_mul, Circle.norm_coe, mul_one]
    ring
  apply actual_circle_map_degree_of_power_homotopy m 1
  have hmap : m = (⟨fun z : Circle => u * z ^ (1 : ℤ), by fun_prop⟩ : C(Circle,Circle)) := by
    ext z
    simpa using congrArg (fun v : Circle => (v : ℂ)) (heq z)
  rw [hmap]
  exact actual_circle_mul_power_homotopic u 1

private theorem actual_real_combo_negative_degree (c : ℂ) (hc : c ≠ 0)
    (m : C(Circle,Circle))
    (hm : ∀ z, (m z : ℂ) =
      (((z : ℂ).re : ℂ) * c + ((z : ℂ).im : ℂ) * (-c * Complex.I)) /
        (‖(((z : ℂ).re : ℂ) * c + ((z : ℂ).im : ℂ) * (-c * Complex.I))‖ : ℂ)) :
    actualCircleMapDegree m = -1 := by
  let u : Circle := actualNormalize c hc
  have heq (z : Circle) : m z = u * z⁻¹ := by
    apply Circle.coe_injective
    rw [hm z, Circle.coe_mul, actualNormalize_coe, Circle.coe_inv_eq_conj]
    have hlin : (((z : ℂ).re : ℂ) * c + ((z : ℂ).im : ℂ) * (-c * Complex.I)) =
        c * (starRingEnd ℂ) (z : ℂ) := by
      have hconj : (((z : ℂ).re : ℂ) - ((z : ℂ).im : ℂ) * Complex.I) =
          (starRingEnd ℂ) (z : ℂ) := by
        apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
      calc
        _ = c * (((z : ℂ).re : ℂ) - ((z : ℂ).im : ℂ) * Complex.I) := by ring
        _ = c * (starRingEnd ℂ) (z : ℂ) := by rw [hconj]
    rw [hlin, norm_mul, RCLike.norm_conj, Circle.norm_coe, mul_one]
    ring
  apply actual_circle_map_degree_of_power_homotopy m (-1)
  have hmap : m = (⟨fun z : Circle => u * z ^ (-1 : ℤ), by fun_prop⟩ : C(Circle,Circle)) := by
    ext z
    simpa using congrArg (fun v : Circle => (v : ℂ)) (heq z)
  rw [hmap]
  exact actual_circle_mul_power_homotopic u (-1)

private theorem actual_real_linear_circle_degree_sign
    (A : ℂ ≃L[ℝ] ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (f : C(Circle,Circle))
    (hf : ∀ z, (f z : ℂ) =
      A ((ρ : ℂ) * z) / (‖A ((ρ : ℂ) * z)‖ : ℂ)) :
    actualCircleMapDegree f =
      if 0 < (A 1).re * (A Complex.I).im - (A Complex.I).re * (A 1).im
      then 1 else -1 := by
  let c : ℂ := A 1
  let d : ℂ := A Complex.I
  have hc : c ≠ 0 := by
    dsimp [c]
    simpa only [map_zero] using A.injective.ne (one_ne_zero : (1 : ℂ) ≠ 0)
  have hdet : c.re * d.im - d.re * c.im ≠ 0 :=
    actual_real_linear_det_ne_zero A
  have hfcombo (z : Circle) : (f z : ℂ) =
      (((z : ℂ).re : ℂ) * c + ((z : ℂ).im : ℂ) * d) /
        (‖(((z : ℂ).re : ℂ) * c + ((z : ℂ).im : ℂ) * d)‖ : ℂ) := by
    have hscale : A ((ρ : ℂ) * (z : ℂ)) = (ρ : ℂ) * A (z : ℂ) := by
      simpa [smul_eq_mul] using (A.map_smul ρ (z : ℂ))
    calc
      (f z : ℂ) = A ((ρ : ℂ) * z) / (‖A ((ρ : ℂ) * z)‖ : ℂ) := hf z
      _ = A (z : ℂ) / (‖A (z : ℂ)‖ : ℂ) := by
        rw [hscale]
        exact actual_normalized_pos_smul ρ hρ _
      _ = _ := by rw [actual_real_linear_apply]
  by_cases hpos : 0 < c.re * d.im - d.re * c.im
  · have hpath (t : CurveComplex.Interval) :
        c.re * (((1 - (t : ℝ) : ℝ) : ℂ) * d + (t : ℂ) * (c * Complex.I)).im -
          (((1 - (t : ℝ) : ℝ) : ℂ) * d + (t : ℂ) * (c * Complex.I)).re * c.im ≠ 0 := by
      rw [actual_det_interp, actual_det_mul_I]
      have ht := t.property
      have hnorm : 0 < ‖c‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hc)
      by_cases ht1 : (t : ℝ) = 1
      · rw [ht1]
        simpa using hnorm.ne'
      · have hlt1 : (t : ℝ) < 1 := lt_of_le_of_ne ht.2 ht1
        have hleft : 0 < 1 - (t : ℝ) := sub_pos.mpr hlt1
        have htotal : 0 < (1 - (t : ℝ)) * (c.re * d.im - d.re * c.im) +
            (t : ℝ) * ‖c‖ ^ 2 :=
          add_pos_of_pos_of_nonneg (mul_pos hleft hpos)
            (mul_nonneg ht.1 (sq_nonneg _))
        exact htotal.ne'
    obtain ⟨m, hm, hhom⟩ :=
      actual_real_combo_homotopic c d (c * Complex.I) hpath f hfcombo
    have hdegree := actual_real_combo_positive_degree c hc m hm
    simpa [c, d, hpos] using
      (actual_circle_map_degree_homotopy_invariant f m hhom).trans hdegree
  · have hneg : c.re * d.im - d.re * c.im < 0 :=
      lt_of_le_of_ne (le_of_not_gt hpos) hdet
    have hpath (t : CurveComplex.Interval) :
        c.re * (((1 - (t : ℝ) : ℝ) : ℂ) * d + (t : ℂ) * (-c * Complex.I)).im -
          (((1 - (t : ℝ) : ℝ) : ℂ) * d + (t : ℂ) * (-c * Complex.I)).re * c.im ≠ 0 := by
      rw [actual_det_interp, actual_det_neg_mul_I]
      have ht := t.property
      have hnorm : 0 < ‖c‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hc)
      by_cases ht1 : (t : ℝ) = 1
      · rw [ht1]
        simpa using (neg_ne_zero.mpr hnorm.ne')
      · have hlt1 : (t : ℝ) < 1 := lt_of_le_of_ne ht.2 ht1
        have hleft : 0 < 1 - (t : ℝ) := sub_pos.mpr hlt1
        have htotal : (1 - (t : ℝ)) * (c.re * d.im - d.re * c.im) +
            (t : ℝ) * -(‖c‖ ^ 2) < 0 :=
          add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg hleft hneg)
            (mul_nonpos_of_nonneg_of_nonpos ht.1 (neg_nonpos.mpr (sq_nonneg _)))
        exact htotal.ne
    obtain ⟨m, hm, hhom⟩ :=
      actual_real_combo_homotopic c d (-c * Complex.I) hpath f hfcombo
    have hdegree := actual_real_combo_negative_degree c hc m hm
    simpa [c, d, hpos] using
      (actual_circle_map_degree_homotopy_invariant f m hhom).trans hdegree

-- Private independent source obligation: Milnor section 6, nondegenerate local index.
private theorem actual_real_nondegenerate_zero_literal_circle_index
    (g : C(ℂ,ℂ)) (A : ℂ ≃L[ℝ] ℂ)
    (hg0 : g 0 = 0) (hderiv : HasFDerivAt g A.toContinuousLinearMap 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ ρ : ℝ, 0 < ρ → ρ < r →
      (∀ z : Circle, g ((ρ:ℂ)*z) ≠ 0) ∧
      ∀ f : C(Circle,Circle),
        (∀ z, (f z : ℂ) = g ((ρ:ℂ)*z)/(‖g ((ρ:ℂ)*z)‖:ℂ)) →
        actualCircleMapDegree f =
          if 0 < (A 1).re * (A Complex.I).im - (A Complex.I).re * (A 1).im
          then 1 else -1 := by
  obtain ⟨r, hr, herror⟩ := actual_real_linear_dominates_error g A hg0 hderiv
  refine ⟨r, hr, ?_⟩
  intro ρ hρ hρr
  have hnear (z : Circle) :
      ‖g ((ρ : ℂ) * z) - A ((ρ : ℂ) * z)‖ < ‖A ((ρ : ℂ) * z)‖ := by
    have hx : (ρ : ℂ) * (z : ℂ) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast ne_of_gt hρ) z.coe_ne_zero
    have hnorm : ‖(ρ : ℂ) * (z : ℂ)‖ = ρ := by
      simp [Complex.norm_real, abs_of_pos hρ]
    exact herror _ hx (hnorm.trans_lt hρr)
  constructor
  · intro z hz
    have hlt := hnear z
    rw [hz, zero_sub, norm_neg] at hlt
    exact (lt_irrefl _ hlt)
  · intro f hf
    obtain ⟨m, hm, hhom⟩ := actual_boundary_homotopic_linear g A ρ hρ hnear f hf
    exact (actual_circle_map_degree_homotopy_invariant f m hhom).trans
      (actual_real_linear_circle_degree_sign A ρ hρ m hm)
