import CurveComplexGenusTwo.Topology.ActualSmoothMorseNormalForm.ActualSmoothCompletingSquares
import CurveComplexGenusTwo.Topology.ActualSmoothMorseNormalForm.MorseHessianIntegralSmoothness
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open scoped ContDiff Topology
open Filter Set

private theorem complex_linear_det (T : ℂ →L[ℝ] ℂ) :
    T.det = (T 1).re * (T Complex.I).im - (T Complex.I).re * (T 1).im := by
  have hm : T.toLinearMap.toMatrix Complex.basisOneI Complex.basisOneI =
      !![(T 1).re, (T Complex.I).re; (T 1).im, (T Complex.I).im] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr, Complex.coe_basisOneI]
  change T.toLinearMap.det = _
  rw [← LinearMap.det_toMatrix Complex.basisOneI, hm, Matrix.det_fin_two_of]

private theorem critical_taylor_integral (f : ℂ → ℝ) (U : Set ℂ) (z₀ : ℂ)
    (hU : IsOpen U) (hz₀ : z₀ ∈ U) (hf : ContDiffOn ℝ ∞ f U)
    (hcritical : gradient f z₀ = 0) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball z₀ r ⊆ U ∧
      ∀ z ∈ Metric.ball z₀ r,
        f z = f z₀ + ∫ t : ℝ in 0..1,
          (1 - t) * (fderiv ℝ (fderiv ℝ f) (z₀ + t • (z - z₀))) (z - z₀) (z - z₀) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz₀)
  have hfder : fderiv ℝ f z₀ = 0 := by
    rw [← toDual_gradient, hcritical, map_zero]
  refine ⟨r, hr, hball, ?_⟩
  intro z hz
  have hseg : ∀ t : ℝ, t ∈ Icc 0 1 → z₀ + t • (z - z₀) ∈ U := by
    intro t ht
    apply hball
    exact (convex_ball z₀ r).add_smul_mem (Metric.mem_ball_self hr)
      (show z₀ + (z - z₀) ∈ Metric.ball z₀ r by simpa using hz) ht
  have htaylor := map_add_eq_sum_add_integral_iteratedFDeriv
    (f := f) (x := z₀) (y := z - z₀) (n := 1)
    (fun t ht => ((hf _ (hseg t ht)).contDiffAt (hU.mem_nhds (hseg t ht))).of_le (by norm_num))
  simp only [Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, one_smul,
    iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply, hfder,
    ContinuousLinearMap.zero_apply, add_zero, add_sub_cancel, pow_one, smul_eq_mul, one_mul, mul_zero] at htaylor
  rw [htaylor]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  simp only [iteratedFDeriv_two_apply]

private theorem integrated_hessian_entry_center (f : ℂ → ℝ) (z₀ v w : ℂ) :
    (∫ t : ℝ in 0..1,
      (1 - t) * fderiv ℝ (fderiv ℝ f) (z₀ + t • (z₀ - z₀)) v w) =
      (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) z₀ v w := by
  simp only [sub_self, smul_zero, add_zero]
  rw [intervalIntegral.integral_mul_const]
  congr 1
  rw [intervalIntegral.integral_sub (f := fun _ : ℝ => 1) (g := fun t : ℝ => t)
    (continuous_const.intervalIntegrable _ _) (continuous_id.intervalIntegrable _ _),
    intervalIntegral.integral_const, integral_id]
  norm_num

private theorem complex_bilinear_expand (H : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (u : ℂ) :
    H u u = u.re ^ 2 * H 1 1 + u.re * u.im * (H 1 Complex.I + H Complex.I 1) +
      u.im ^ 2 * H Complex.I Complex.I := by
  have hu : u = u.re • (1 : ℂ) + u.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hu]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  ring

private theorem critical_scalar_coefficients (f : ℂ → ℝ) (U : Set ℂ) (z₀ : ℂ)
    (hU : IsOpen U) (hz₀ : z₀ ∈ U) (hf : ContDiffOn ℝ ∞ f U)
    (hcritical : gradient f z₀ = 0) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball z₀ r ⊆ U ∧
      ∀ z ∈ Metric.ball z₀ r,
        let H := fun v w : ℂ => ∫ t : ℝ in 0..1,
          (1 - t) * fderiv ℝ (fderiv ℝ f) (z₀ + t • (z - z₀)) v w
        f z = f z₀ + (z - z₀).re ^ 2 * H 1 1 +
          (z - z₀).re * (z - z₀).im * (H 1 Complex.I + H Complex.I 1) +
          (z - z₀).im ^ 2 * H Complex.I Complex.I := by
  obtain ⟨r, hr, hball, htaylor⟩ := critical_taylor_integral f U z₀ hU hz₀ hf hcritical
  refine ⟨r, hr, hball, ?_⟩
  intro z hz
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, z₀ + t • (z - z₀) ∈ U := by
    intro t ht
    exact hball ((convex_ball z₀ r).add_smul_mem (Metric.mem_ball_self hr)
      (show z₀ + (z - z₀) ∈ Metric.ball z₀ r by simpa using hz) ht)
  let h := fun (v w : ℂ) (t : ℝ) =>
    (1 - t) * fderiv ℝ (fderiv ℝ f) (z₀ + t • (z - z₀)) v w
  have hint : ∀ v w, IntervalIntegrable (h v w) MeasureTheory.volume 0 1 := by
    intro v w
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    intro t ht
    have hft : ContDiffAt ℝ ∞ f (z₀ + t • (z - z₀)) :=
      (hf _ (hseg t ht)).contDiffAt (hU.mem_nhds (hseg t ht))
    have hc := ((hft.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).continuousAt
    have hv := (hc.clm_apply (show ContinuousAt (fun _ : ℂ => v) _ from continuousAt_const)).clm_apply (show ContinuousAt (fun _ : ℂ => w) _ from continuousAt_const)
    exact ((show ContinuousAt (fun t : ℝ => 1 - t) t by fun_prop).mul
      (hv.comp (f := fun t : ℝ => z₀ + t • (z - z₀)) (by fun_prop))).continuousWithinAt
  have hexp : (fun t => (1 - t) *
      fderiv ℝ (fderiv ℝ f) (z₀ + t • (z - z₀)) (z - z₀) (z - z₀)) =
      fun t => (z - z₀).re ^ 2 * h 1 1 t +
        ((z - z₀).re * (z - z₀).im) * (h 1 Complex.I t + h Complex.I 1 t) +
        (z - z₀).im ^ 2 * h Complex.I Complex.I t := by
    funext t
    rw [complex_bilinear_expand]
    dsimp [h]
    ring
  rw [htaylor z hz, hexp]
  rw [intervalIntegral.integral_add
    ((hint 1 1).const_mul _ |>.add ((hint 1 Complex.I).add (hint Complex.I 1) |>.const_mul _))
    ((hint Complex.I Complex.I).const_mul _),
    intervalIntegral.integral_add ((hint 1 1).const_mul _)
      ((hint 1 Complex.I).add (hint Complex.I 1) |>.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hint 1 Complex.I) (hint Complex.I 1)]
  dsimp [h]
  ring

theorem actual_complex_smooth_morse_normal_form
    (f : ℂ → ℝ) (U : Set ℂ) (z₀ : ℂ)
    (hU : IsOpen U) (hz₀ : z₀ ∈ U)
    (hf : ContDiffOn ℝ ∞ f U)
    (hcritical : gradient f z₀ = 0)
    (hnondegenerate : (fderiv ℝ (gradient f) z₀).det ≠ 0) :
    ∃ (k : Fin 3) (e : OpenPartialHomeomorph ℂ ℂ),
      IsActualComplexSmoothMorseNormalForm f U z₀ k e := by
  have hfAt : ContDiffAt ℝ ∞ f z₀ := (hf z₀ hz₀).contDiffAt (hU.mem_nhds hz₀)
  obtain ⟨r, hr, hball, hcoeff⟩ := critical_scalar_coefficients f U z₀ hU hz₀ hf hcritical
  let H : ℂ → ℂ → ℂ → ℝ := fun v w z => ∫ t : ℝ in 0..1,
    (1 - t) * fderiv ℝ (fderiv ℝ f) (z₀ + t • (z - z₀)) v w
  have hH0 (v w : ℂ) : H v w z₀ = (1 / 2 : ℝ) *
      inner ℝ (fderiv ℝ (gradient f) z₀ v) w := by
    rw [actual_complex_scalar_gradient_derivative_pairing f z₀ (hfAt.of_le (by simp))]
    exact integrated_hessian_entry_center f z₀ v w
  have hHsym (v w : ℂ) : H v w z₀ = H w v z₀ := by
    rw [hH0, hH0, actual_complex_scalar_gradient_derivative_pairing f z₀ (hfAt.of_le (by simp)),
      actual_complex_scalar_gradient_derivative_pairing f z₀ (hfAt.of_le (by simp)),
      (hfAt.of_le (by simp : (2 : WithTop ℕ∞) ≤ ∞)).isSymmSndFDerivAt (by norm_num) v w]
  have hcoeffdet : H 1 1 z₀ * H Complex.I Complex.I z₀ -
      ((H 1 Complex.I z₀ + H Complex.I 1 z₀) / 2) ^ 2 ≠ 0 := by
    have hh : (fderiv ℝ (gradient f) z₀).det = 4 *
        (H 1 1 z₀ * H Complex.I Complex.I z₀ -
          ((H 1 Complex.I z₀ + H Complex.I 1 z₀) / 2) ^ 2) := by
      have hcross := hHsym 1 Complex.I
      simp only [hH0, Complex.inner, one_mul, Complex.conj_re, Complex.I_mul_re,
        Complex.conj_im, neg_neg] at hcross ⊢
      rw [complex_linear_det]
      nlinarith
    intro hz
    exact hnondegenerate (by rw [hh, hz, mul_zero])
  have hHs (v w : ℂ) : ContDiffOn ℝ ∞ (H v w) (Metric.ball z₀ r) :=
    actual_complex_hessian_integral_contDiffOn f z₀ r hr (hf.mono hball) v w
  let V : Set ℂ := (fun w : ℂ => z₀ + w) ⁻¹' Metric.ball z₀ r
  have hV : IsOpen V := Metric.isOpen_ball.preimage (by fun_prop)
  have h0 : (0 : ℂ) ∈ V := by simpa [V] using (Metric.mem_ball_self hr : z₀ ∈ Metric.ball z₀ r)
  have htrans : ContDiffOn ℝ ∞ (fun w : ℂ => z₀ + w) V :=
    contDiffOn_const.add contDiffOn_id
  have hHt (v w : ℂ) : ContDiffOn ℝ ∞ (fun u => H v w (z₀ + u)) V :=
    (hHs v w).comp htrans (fun _ hx => hx)
  let a : ℂ → ℝ := fun w => H 1 1 (z₀ + w)
  let b : ℂ → ℝ := fun w => (H 1 Complex.I (z₀ + w) + H Complex.I 1 (z₀ + w)) / 2
  let c : ℂ → ℝ := fun w => H Complex.I Complex.I (z₀ + w)
  have ha : ContDiffOn ℝ ∞ a V := hHt 1 1
  have hb : ContDiffOn ℝ ∞ b V := ((hHt 1 Complex.I).add (hHt Complex.I 1)).div_const 2
  have hc : ContDiffOn ℝ ∞ c V := hHt Complex.I Complex.I
  have hd : a 0 * c 0 - (b 0)^2 ≠ 0 := by simpa [a, b, c] using hcoeffdet
  obtain ⟨k, e₀, he₀⟩ := actual_complex_smooth_quadratic_coefficients_normal_form
    a b c V hV h0 ha hb hc hd
  let τ : OpenPartialHomeomorph ℂ ℂ := (Homeomorph.addRight (-z₀)).toOpenPartialHomeomorph
  have hτ (z : ℂ) : τ z = z - z₀ := rfl
  have hτi (z : ℂ) : τ.symm z = z + z₀ := by
    change z - (-z₀) = z + z₀
    simp
  let e := τ.trans e₀
  have he_source (z : ℂ) (hz : z ∈ e.source) : z ∈ Metric.ball z₀ r := by
    have hz' := he₀.source_subset hz.2
    change z₀ + (z - z₀) ∈ Metric.ball z₀ r at hz'
    simpa using hz'
  refine ⟨k, e, ?_⟩
  refine {
    center_mem_source := ?_
    source_subset := fun z hz => hball (he_source z hz)
    center_eq_zero := ?_
    contDiffOn := ?_
    contDiffOn_symm := ?_
    normal_form := ?_ }
  · exact ⟨Set.mem_univ _, by simpa [hτ] using he₀.center_mem_source⟩
  · change e₀ (τ z₀) = 0
    simpa [hτ] using he₀.center_eq_zero
  · change ContDiffOn ℝ ∞ (e₀ ∘ τ) e.source
    apply he₀.contDiffOn.comp _ (fun z hz => hz.2)
    change ContDiffOn ℝ ∞ (fun z : ℂ => z-z₀) e.source
    exact contDiffOn_id.sub contDiffOn_const
  · change ContDiffOn ℝ ∞ (τ.symm ∘ e₀.symm) e.target
    have hτs : ContDiffOn ℝ ∞ τ.symm Set.univ := by
      have heq : (τ.symm : ℂ → ℂ) = fun z => z+z₀ := funext hτi
      rw [heq]
      exact contDiffOn_id.add contDiffOn_const
    exact hτs.comp (he₀.contDiffOn_symm.mono (fun z hz => hz.1)) (fun _ _ => Set.mem_univ _)
  · intro z hz
    have hh := he₀.normal_form (z-z₀) hz.2
    have hq := hcoeff z (he_source z hz)
    change f z = f z₀ + actualComplexMorseQuadratic k (e₀ (z-z₀))
    simp only [Complex.zero_re, Complex.zero_im, zero_pow (by decide : 2 ≠ 0),
      mul_zero, add_zero, zero_add] at hh
    rw [← hh]
    dsimp [a, b, c]
    simp only [add_sub_cancel]
    change f z = f z₀ + (H 1 1 z * (z-z₀).re^2 +
      2 * ((H 1 Complex.I z + H Complex.I 1 z) / 2) * (z-z₀).re * (z-z₀).im +
      H Complex.I Complex.I z * (z-z₀).im^2)
    rw [hq]
    dsimp [H]
    ring
