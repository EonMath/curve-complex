import CurveComplexGenusTwo.Topology.ActualLocalDbarSolvability.KernelCalculus
import CurveComplexGenusTwo.Topology.ActualLocalDbarSolvability.SourceReviewRequests
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open scoped ContDiff Real ComplexConjugate
open MeasureTheory Set Complex Filter

namespace CanonicalDimensionTwo.LocalDbar

private theorem real_linear_polar (L : ℂ →L[ℝ] ℂ) (u : ℂ) :
    L u + Complex.I * L (Complex.I * u) =
      conj u * (L 1 + Complex.I * L Complex.I) := by
  have h (v : ℂ) : L v = v.re • L 1 + v.im • L Complex.I := by
    conv_lhs => rw [← Complex.re_add_im v]
    rw [map_add]
    congr 1
    · simpa using L.map_smul v.re (1 : ℂ)
    · simpa using L.map_smul v.im Complex.I
  rw [h u, h (Complex.I * u)]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    zero_sub, Complex.mul_im, zero_add, Complex.real_smul]
  rw [← Complex.re_add_im (conj u)]
  simp only [Complex.conj_re, Complex.conj_im, Complex.ofReal_neg]
  ring_nf
  simp

private theorem polar_integrand (L : ℂ →L[ℝ] ℂ) {r : ℝ} (hr : r ≠ 0) (θ : ℝ) :
    r • ((circleMap 0 r θ)⁻¹ * ((L 1 + Complex.I * L Complex.I) / 2)) =
      (L (circleMap 0 1 θ) + Complex.I * L (Complex.I * circleMap 0 1 θ)) / 2 := by
  rw [real_linear_polar, conj_circleMap_zero, circleMap_zero_inv]
  simp only [Complex.real_smul, circleMap_zero, ofReal_one, one_mul, ofReal_inv]
  have hr' : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr
  field_simp

private theorem radial_hasDerivAt {g : ℂ → ℂ} (hg : Differentiable ℝ g)
    (r θ : ℝ) :
    HasDerivAt (fun t : ℝ => g (circleMap 0 t θ))
      (fderiv ℝ g (circleMap 0 r θ) (circleMap 0 1 θ)) r := by
  apply (hg _).hasFDerivAt.comp_hasDerivAt
  simpa [circleMap] using (Complex.ofRealCLM.hasDerivAt (x := r)).mul_const
    (Complex.exp ((θ : ℂ) * Complex.I))

private theorem angular_hasDerivAt {g : ℂ → ℂ} (hg : Differentiable ℝ g)
    (r θ : ℝ) :
    HasDerivAt (fun t : ℝ => g (circleMap 0 r t))
      ((r : ℂ) * fderiv ℝ g (circleMap 0 r θ)
        (Complex.I * circleMap 0 1 θ)) θ := by
  convert (hg _).hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_circleMap 0 r θ) using 1
  · rfl
  · rw [← Complex.real_smul, ← map_smul]
    congr 1
    simp [circleMap, Complex.real_smul, mul_comm, mul_left_comm]

private theorem polarCoord_symm_circle (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
  apply Complex.ext <;> simp [Complex.polarCoord_symm_apply, circleMap_zero_re,
    circleMap_zero_im, -Complex.ofReal_cos, -Complex.ofReal_sin]

private theorem integral_angular_eq_zero {g : ℂ → ℂ}
    (hg : ContDiff ℝ ∞ g) {r : ℝ} (hr : r ≠ 0) :
    (∫ θ in -Real.pi..Real.pi,
      fderiv ℝ g (circleMap 0 r θ) (Complex.I * circleMap 0 1 θ)) = 0 := by
  have hc : Continuous (fun θ : ℝ =>
      fderiv ℝ g (circleMap 0 r θ) (Complex.I * circleMap 0 1 θ)) := by
    exact (((hg.of_le (by simp) : ContDiff ℝ 1 g).continuous_fderiv one_ne_zero).comp
      (contDiff_circleMap 0 r (n := 1)).continuous).clm_apply
        (continuous_const.mul (contDiff_circleMap 0 1 (n := 1)).continuous)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ _ => angular_hasDerivAt (hg.differentiable (by simp)) r θ)
    ((continuous_const.mul hc).intervalIntegrable (-Real.pi) Real.pi)
  rw [intervalIntegral.integral_const_mul] at h
  have he : circleMap 0 r Real.pi = circleMap 0 r (-Real.pi) := by
    apply Complex.ext <;> simp [circleMap_zero_re, circleMap_zero_im]
  rw [he, sub_self] at h
  exact (mul_eq_zero.mp h).resolve_left (ofReal_ne_zero.mpr hr)

private theorem integral_radial {g : ℂ → ℂ}
    (hg : ContDiff ℝ ∞ g) (R θ : ℝ) :
    (∫ r in 0..R, fderiv ℝ g (circleMap 0 r θ) (circleMap 0 1 θ)) =
      g (circleMap 0 R θ) - g 0 := by
  have hc : Continuous (fun r : ℝ =>
      fderiv ℝ g (circleMap 0 r θ) (circleMap 0 1 θ)) := by
    apply (((hg.of_le (by simp) : ContDiff ℝ 1 g).continuous_fderiv one_ne_zero).comp
      (show Continuous (fun r : ℝ => circleMap 0 r θ) by
        simp only [circleMap]; fun_prop)).clm_apply continuous_const
  simpa [circleMap] using intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => radial_hasDerivAt (hg.differentiable (by simp)) r θ)
    (hc.intervalIntegrable 0 R)

private theorem continuous_polar_derivatives {g : ℂ → ℂ}
    (hg : ContDiff ℝ ∞ g) :
    Continuous (fun p : ℝ × ℝ => fderiv ℝ g (circleMap 0 p.1 p.2)
      (circleMap 0 1 p.2)) ∧
    Continuous (fun p : ℝ × ℝ => fderiv ℝ g (circleMap 0 p.1 p.2)
      (Complex.I * circleMap 0 1 p.2)) := by
  have hp : Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by
    simp only [circleMap]; fun_prop
  have hd := ((hg.of_le (by simp) : ContDiff ℝ 1 g).continuous_fderiv one_ne_zero).comp hp
  have he : Continuous (fun p : ℝ × ℝ => circleMap 0 1 p.2) :=
    (contDiff_circleMap 0 1 (n := 1)).continuous.comp continuous_snd
  exact ⟨hd.clm_apply he, hd.clm_apply (continuous_const.mul he)⟩

private theorem integral_polar_derivatives {g : ℂ → ℂ}
    (hg : ContDiff ℝ ∞ g) (R : ℝ) :
    (∫ r in 0..R, ∫ θ in -Real.pi..Real.pi,
      (fderiv ℝ g (circleMap 0 r θ) (circleMap 0 1 θ) +
      Complex.I * fderiv ℝ g (circleMap 0 r θ) (Complex.I * circleMap 0 1 θ)) / 2) =
      (∫ θ in -Real.pi..Real.pi, g (circleMap 0 R θ) - g 0) / 2 := by
  obtain ⟨hA, hB⟩ := continuous_polar_derivatives hg
  have inner (r : ℝ) (hr : r ≠ 0) :
      (∫ θ in -Real.pi..Real.pi,
        (fderiv ℝ g (circleMap 0 r θ) (circleMap 0 1 θ) +
        Complex.I * fderiv ℝ g (circleMap 0 r θ) (Complex.I * circleMap 0 1 θ)) / 2) =
      (∫ θ in -Real.pi..Real.pi,
        fderiv ℝ g (circleMap 0 r θ) (circleMap 0 1 θ)) / 2 := by
    have hAr : Continuous (fun θ : ℝ =>
        fderiv ℝ g (circleMap 0 r θ) (circleMap 0 1 θ)) :=
      hA.comp (continuous_const.prodMk continuous_id)
    have hBr : Continuous (fun θ : ℝ =>
        Complex.I * fderiv ℝ g (circleMap 0 r θ) (Complex.I * circleMap 0 1 θ)) :=
      continuous_const.mul (hB.comp (continuous_const.prodMk continuous_id))
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add
      (hAr.intervalIntegrable _ _) (hBr.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, integral_angular_eq_zero hg hr,
      mul_zero, add_zero]
  calc
    _ = ∫ r in 0..R, (∫ θ in -Real.pi..Real.pi,
        fderiv ℝ g (circleMap 0 r θ) (circleMap 0 1 θ)) / 2 := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [volume.ae_ne (0 : ℝ)] with r hr
      exact fun _ => inner r hr
    _ = (∫ r in 0..R, ∫ θ in -Real.pi..Real.pi,
        fderiv ℝ g (circleMap 0 r θ) (circleMap 0 1 θ)) / 2 :=
      intervalIntegral.integral_div (2 : ℂ) _
    _ = (∫ θ in -Real.pi..Real.pi, ∫ r in 0..R,
        fderiv ℝ g (circleMap 0 r θ) (circleMap 0 1 θ)) / 2 := by
      rw [intervalIntegral_intervalIntegral_swap]
      exact (hA.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
        (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
    _ = _ := by simp_rw [integral_radial hg]

private theorem compact_integral_inv_dbar {g : ℂ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    (∫ w : ℂ, w⁻¹ * dbar g w) = -(Real.pi : ℂ) * g 0 := by
  obtain ⟨R, hR, hbound⟩ := hc.isCompact.isBounded.exists_pos_norm_lt
  have hout (w : ℂ) (hw : R ≤ ‖w‖) : w ∉ tsupport g :=
    fun hm => (not_lt_of_ge hw) (hbound w hm)
  have hzero (w : ℂ) (hw : R ≤ ‖w‖) : g w = 0 :=
    image_eq_zero_of_notMem_tsupport (hout w hw)
  have hd (w : ℂ) (hw : R ≤ ‖w‖) : fderiv ℝ g w = 0 :=
    fderiv_of_notMem_tsupport ℝ (hout w hw)
  let P : ℝ × ℝ → ℂ := fun p =>
    (fderiv ℝ g (circleMap 0 p.1 p.2) (circleMap 0 1 p.2) +
    Complex.I * fderiv ℝ g (circleMap 0 p.1 p.2) (Complex.I * circleMap 0 1 p.2)) / 2
  have hP : Continuous P := by
    obtain ⟨hA, hB⟩ := continuous_polar_derivatives hg
    exact (hA.add (continuous_const.mul hB)).div_const 2
  have hPint : IntegrableOn P (Ioc 0 R ×ˢ Ioo (-Real.pi) Real.pi) :=
    (hP.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioo_subset_Icc_self)
  calc
    _ = ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        p.1 • ((circleMap 0 p.1 p.2)⁻¹ * dbar g (circleMap 0 p.1 p.2)) := by
      simpa only [polarCoord_target, polarCoord_symm_circle] using
        (Complex.integral_comp_polarCoord_symm (fun w : ℂ => w⁻¹ * dbar g w)).symm
    _ = ∫ p in Ioc (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi,
        p.1 • ((circleMap 0 p.1 p.2)⁻¹ * dbar g (circleMap 0 p.1 p.2)) := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        (measurableSet_Ioi.prod measurableSet_Ioo) (Set.prod_mono Ioc_subset_Ioi_self Subset.rfl)
      intro p hp
      have hpr : R < p.1 := by
        by_contra h
        exact hp.2 ⟨⟨hp.1.1, not_lt.mp h⟩, hp.1.2⟩
      have hn : R ≤ ‖circleMap 0 p.1 p.2‖ := by
        simpa only [norm_circleMap_zero, abs_of_pos (show 0 < p.1 from hp.1.1)] using hpr.le
      simp [dbar, hd _ hn]
    _ = ∫ p in Ioc (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi, P p := by
      apply setIntegral_congr_fun (measurableSet_Ioc.prod measurableSet_Ioo)
      intro p hp
      exact polar_integrand _ (ne_of_gt hp.1.1) p.2
    _ = ∫ r in Ioc (0 : ℝ) R, ∫ θ in Ioo (-Real.pi) Real.pi, P (r, θ) := by
      rw [Measure.volume_eq_prod] at hPint ⊢
      exact setIntegral_prod P hPint
    _ = ∫ r in 0..R, ∫ θ in -Real.pi..Real.pi, P (r, θ) := by
      simp_rw [intervalIntegral.integral_of_le hR.le,
        intervalIntegral.integral_of_le (neg_le_self Real.pi_pos.le), integral_Ioc_eq_integral_Ioo]
    _ = (∫ θ in -Real.pi..Real.pi, g (circleMap 0 R θ) - g 0) / 2 :=
      integral_polar_derivatives hg R
    _ = -(Real.pi : ℂ) * g 0 := by
      have hz (θ : ℝ) : g (circleMap 0 R θ) = 0 :=
        hzero _ (by simp only [norm_circleMap_zero, abs_of_pos hR, le_refl])
      simp_rw [hz, zero_sub]
      rw [intervalIntegral.integral_const]
      simp only [sub_neg_eq_add, Complex.real_smul, Complex.ofReal_add]
      ring

theorem compactCauchyIdentity : SourceReviewRequests.CompactCauchyIdentityStatement := by
  intro g hg hc z
  let h : ℂ → ℂ := fun w => g (z - w)
  have hh : ContDiff ℝ ∞ h := hg.comp (contDiff_const.sub contDiff_id)
  have hhc : HasCompactSupport h := hc.comp_homeomorph (Homeomorph.subLeft z)
  have hdf (w : ℂ) : fderiv ℝ h w = -fderiv ℝ g (z - w) := by
    have hdg := (hg.differentiable (by simp) (z - w)).hasFDerivAt
    have hds := (hasFDerivAt_const (𝕜 := ℝ) z w).sub (hasFDerivAt_id w)
    change fderiv ℝ (g ∘ fun v : ℂ => z - v) w = _
    rw [(hdg.comp w hds).fderiv]
    ext v
    simp
  have hdb (w : ℂ) : dbar h w = -dbar g (z - w) := by
    simp only [dbar, hdf, neg_apply]
    ring
  have hi := compact_integral_inv_dbar hh hhc
  simp_rw [hdb, mul_neg, integral_neg] at hi
  simpa only [h, sub_zero, neg_mul, neg_inj] using hi

theorem compactCauchyTransform : SourceReviewRequests.CompactCauchyTransformStatement := by
  intro g hg hc
  refine ⟨contDiff_pi_inv_integral hg hc, ?_⟩
  intro z
  rw [dbar_pi_inv_integral hg hc z, compactCauchyIdentity g hg hc z]
  rw [← mul_assoc, inv_mul_cancel₀ (ofReal_ne_zero.mpr Real.pi_ne_zero), one_mul]

end CanonicalDimensionTwo.LocalDbar
