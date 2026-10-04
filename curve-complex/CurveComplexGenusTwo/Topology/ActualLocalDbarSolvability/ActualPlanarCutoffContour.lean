import CurveComplexGenusTwo.Topology.ActualLocalDbarSolvability.ActualPlanarCutoffContourStatement
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.Complex.Conformal
import Mathlib.MeasureTheory.Group.Integral

open TopologicalSpace MeasureTheory Filter Set Complex
open scoped ContDiff Distributions Topology Real ComplexConjugate
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace CanonicalDimensionTwo.LocalDbar

/-- The exact approved planar cutoff identity. -/
theorem actualPlanarCutoffContour : ActualPlanarCutoffContourStatement := by
  have hlinear (L : ℂ →L[ℝ] ℂ) (u : ℂ) :
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
  have hpolar (L : ℂ →L[ℝ] ℂ) {r : ℝ} (hr : r ≠ 0) (θ : ℝ) :
      r • ((circleMap 0 r θ)⁻¹ * ((L 1 + Complex.I * L Complex.I) / 2)) =
        (L (circleMap 0 1 θ) + Complex.I * L (Complex.I * circleMap 0 1 θ)) / 2 := by
    rw [hlinear, conj_circleMap_zero, circleMap_zero_inv]
    simp only [Complex.real_smul, circleMap_zero, ofReal_one, one_mul, ofReal_inv]
    have hr' : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr
    field_simp
  have hpolar_circle (p : ℝ × ℝ) :
      Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
    apply Complex.ext <;> simp [Complex.polarCoord_symm_apply, circleMap_zero_re,
      circleMap_zero_im, -Complex.ofReal_cos, -Complex.ofReal_sin]
  have hradial {g : ℂ → ℂ} (r θ : ℝ) (hg : DifferentiableAt ℝ g (circleMap 0 r θ)) :
      HasDerivAt (fun t : ℝ => g (circleMap 0 t θ))
        (fderiv ℝ g (circleMap 0 r θ) (circleMap 0 1 θ)) r := by
    apply hg.hasFDerivAt.comp_hasDerivAt (f := fun t : ℝ => circleMap 0 t θ) r
    simpa [circleMap] using (Complex.ofRealCLM.hasDerivAt (x := r)).mul_const
      (Complex.exp ((θ : ℂ) * Complex.I))
  have hangular {g : ℂ → ℂ} (r θ : ℝ) (hg : DifferentiableAt ℝ g (circleMap 0 r θ)) :
      HasDerivAt (fun t : ℝ => g (circleMap 0 r t))
        ((r : ℂ) * fderiv ℝ g (circleMap 0 r θ)
          (Complex.I * circleMap 0 1 θ)) θ := by
    convert hg.hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_circleMap 0 r θ) using 1
    · rfl
    · rw [← Complex.real_smul, ← map_smul]
      congr 1
      simp [circleMap, Complex.real_smul, mul_comm, mul_left_comm]
  have hne {r : ℝ} (hr : r ≠ 0) (θ : ℝ) : circleMap 0 r θ ≠ 0 :=
    circleMap_ne_center hr
  have hpolar_cont {g : ℂ → ℂ}
      (hg : ∀ z ≠ 0, ContDiffAt ℝ ∞ g z) (p : ℝ × ℝ) (hp : p.1 ≠ 0) :
      ContinuousAt (fun q : ℝ × ℝ => fderiv ℝ g (circleMap 0 q.1 q.2)
        (circleMap 0 1 q.2)) p ∧
      ContinuousAt (fun q : ℝ × ℝ => fderiv ℝ g (circleMap 0 q.1 q.2)
        (Complex.I * circleMap 0 1 q.2)) p := by
    have hc : Continuous (fun q : ℝ × ℝ => circleMap 0 q.1 q.2) := by
      simp only [circleMap]; fun_prop
    have hd := ((hg _ (hne hp p.2)).fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ ∞ by simp)).continuousAt.comp (f := fun q : ℝ × ℝ => circleMap 0 q.1 q.2) hc.continuousAt
    have he : Continuous (fun q : ℝ × ℝ => circleMap 0 1 q.2) :=
      (contDiff_circleMap 0 1 (n := 1)).continuous.comp continuous_snd
    exact ⟨hd.clm_apply he.continuousAt,
      hd.clm_apply (continuous_const.mul he).continuousAt⟩
  have hangular_zero {g : ℂ → ℂ} (hg : ∀ z ≠ 0, ContDiffAt ℝ ∞ g z)
      {r : ℝ} (hr : r ≠ 0) :
      (∫ θ in -Real.pi..Real.pi,
        fderiv ℝ g (circleMap 0 r θ) (Complex.I * circleMap 0 1 θ)) = 0 := by
    have hc : Continuous (fun θ : ℝ =>
        fderiv ℝ g (circleMap 0 r θ) (Complex.I * circleMap 0 1 θ)) := by
      rw [continuous_iff_continuousAt]
      intro θ
      exact (hpolar_cont hg (r, θ) hr).2.comp
        (continuous_const.prodMk continuous_id).continuousAt
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun θ _ => hangular r θ ((hg _ (hne hr θ)).differentiableAt (by simp)))
      ((continuous_const.mul hc).intervalIntegrable (-Real.pi) Real.pi)
    rw [intervalIntegral.integral_const_mul] at h
    have he : circleMap 0 r Real.pi = circleMap 0 r (-Real.pi) := by
      apply Complex.ext <;> simp [circleMap_zero_re, circleMap_zero_im]
    rw [he, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_left (ofReal_ne_zero.mpr hr)
  have hradial_integral {g : ℂ → ℂ} (hg : ∀ z ≠ 0, ContDiffAt ℝ ∞ g z)
      {r S : ℝ} (hr : 0 < r) (hrS : r ≤ S) (θ : ℝ) :
      (∫ t in r..S, fderiv ℝ g (circleMap 0 t θ) (circleMap 0 1 θ)) =
        g (circleMap 0 S θ) - g (circleMap 0 r θ) := by
    have hc : ContinuousOn (fun t : ℝ =>
        fderiv ℝ g (circleMap 0 t θ) (circleMap 0 1 θ)) (uIcc r S) := by
      intro t ht
      have ht0 : t ≠ 0 := ne_of_gt (hr.trans_le ((uIcc_of_le hrS ▸ ht).1))
      exact ((hpolar_cont hg (t, θ) ht0).1.comp (f := fun t : ℝ => (t, θ))
        (continuous_id.prodMk continuous_const).continuousAt).continuousWithinAt
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hradial t θ ((hg _ (hne (ne_of_gt
        (hr.trans_le ((uIcc_of_le hrS ▸ ht).1))) θ)).differentiableAt (by simp)))
      hc.intervalIntegrable
  have hpolar_integral {g : ℂ → ℂ} (hg : ∀ z ≠ 0, ContDiffAt ℝ ∞ g z)
      {r S : ℝ} (hr : 0 < r) (hrS : r ≤ S) :
      (∫ t in r..S, ∫ θ in -Real.pi..Real.pi,
        (fderiv ℝ g (circleMap 0 t θ) (circleMap 0 1 θ) +
        Complex.I * fderiv ℝ g (circleMap 0 t θ) (Complex.I * circleMap 0 1 θ)) / 2) =
        (∫ θ in -Real.pi..Real.pi, g (circleMap 0 S θ) - g (circleMap 0 r θ)) / 2 := by
    have hA : ContinuousOn (fun p : ℝ × ℝ =>
        fderiv ℝ g (circleMap 0 p.1 p.2) (circleMap 0 1 p.2))
        (uIcc r S ×ˢ uIcc (-Real.pi) Real.pi) := by
      intro p hp
      exact (hpolar_cont hg p (ne_of_gt
        (hr.trans_le ((uIcc_of_le hrS ▸ hp.1).1)))).1.continuousWithinAt
    have inner (t : ℝ) (ht : 0 < t) :
        (∫ θ in -Real.pi..Real.pi,
          (fderiv ℝ g (circleMap 0 t θ) (circleMap 0 1 θ) +
          Complex.I * fderiv ℝ g (circleMap 0 t θ) (Complex.I * circleMap 0 1 θ)) / 2) =
          (∫ θ in -Real.pi..Real.pi,
            fderiv ℝ g (circleMap 0 t θ) (circleMap 0 1 θ)) / 2 := by
      have hAt : Continuous (fun θ : ℝ =>
          fderiv ℝ g (circleMap 0 t θ) (circleMap 0 1 θ)) := by
        rw [continuous_iff_continuousAt]
        intro θ
        exact (hpolar_cont hg (t, θ) (ne_of_gt ht)).1.comp
          (continuous_const.prodMk continuous_id).continuousAt
      have hBt : Continuous (fun θ : ℝ =>
          Complex.I * fderiv ℝ g (circleMap 0 t θ) (Complex.I * circleMap 0 1 θ)) := by
        rw [continuous_iff_continuousAt]
        intro θ
        exact continuousAt_const.mul ((hpolar_cont hg (t, θ) (ne_of_gt ht)).2.comp
          (continuous_const.prodMk continuous_id).continuousAt)
      rw [intervalIntegral.integral_div, intervalIntegral.integral_add
        (hAt.intervalIntegrable _ _) (hBt.intervalIntegrable _ _),
        intervalIntegral.integral_const_mul, hangular_zero hg (ne_of_gt ht),
        mul_zero, add_zero]
    calc
      _ = ∫ t in r..S, (∫ θ in -Real.pi..Real.pi,
          fderiv ℝ g (circleMap 0 t θ) (circleMap 0 1 θ)) / 2 := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact inner t (hr.trans_le ((uIcc_of_le hrS ▸ ht).1))
      _ = (∫ t in r..S, ∫ θ in -Real.pi..Real.pi,
          fderiv ℝ g (circleMap 0 t θ) (circleMap 0 1 θ)) / 2 :=
        intervalIntegral.integral_div (2 : ℂ) _
      _ = (∫ θ in -Real.pi..Real.pi, ∫ t in r..S,
          fderiv ℝ g (circleMap 0 t θ) (circleMap 0 1 θ)) / 2 := by
        rw [intervalIntegral_intervalIntegral_swap]
        exact (hA.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
          (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
      _ = _ := by simp_rw [hradial_integral hg hr hrS]
  have hannulus {g : ℂ → ℂ} (hg : ∀ z ≠ 0, ContDiffAt ℝ ∞ g z)
      {r S : ℝ} (hr : 0 < r) (hrS : r ≤ S)
      (hin : ∀ z ≠ 0, ‖z‖ ≤ r → dbar g z = 0)
      (hout : ∀ z, S ≤ ‖z‖ → dbar g z = 0) :
      (∫ z : ℂ, z⁻¹ * dbar g z) =
        (∫ θ in -Real.pi..Real.pi, g (circleMap 0 S θ) - g (circleMap 0 r θ)) / 2 := by
    let P : ℝ × ℝ → ℂ := fun p =>
      (fderiv ℝ g (circleMap 0 p.1 p.2) (circleMap 0 1 p.2) +
      Complex.I * fderiv ℝ g (circleMap 0 p.1 p.2) (Complex.I * circleMap 0 1 p.2)) / 2
    have hP : ContinuousOn P (Icc r S ×ˢ Icc (-Real.pi) Real.pi) := by
      intro p hp
      obtain ⟨hA, hB⟩ := hpolar_cont hg p (ne_of_gt (hr.trans_le hp.1.1))
      exact ((hA.add (continuousAt_const.mul hB)).div_const 2).continuousWithinAt
    have hPint : IntegrableOn P (Ioc r S ×ˢ Ioo (-Real.pi) Real.pi) :=
      (hP.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
        (Set.prod_mono Ioc_subset_Icc_self Ioo_subset_Icc_self)
    calc
      _ = ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
          p.1 • ((circleMap 0 p.1 p.2)⁻¹ * dbar g (circleMap 0 p.1 p.2)) := by
        simpa only [polarCoord_target, hpolar_circle] using
          (Complex.integral_comp_polarCoord_symm (fun z : ℂ => z⁻¹ * dbar g z)).symm
      _ = ∫ p in Ioc r S ×ˢ Ioo (-Real.pi) Real.pi,
          p.1 • ((circleMap 0 p.1 p.2)⁻¹ * dbar g (circleMap 0 p.1 p.2)) := by
        apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
          (measurableSet_Ioi.prod measurableSet_Ioo)
          (Set.prod_mono (fun _ ht => hr.trans ht.1) Subset.rfl)
        intro p hp
        have hpr : p.1 ≤ r ∨ S < p.1 := by
          by_cases ht : r < p.1
          · exact Or.inr (not_le.mp (fun hS => hp.2 ⟨⟨ht, hS⟩, hp.1.2⟩))
          · exact Or.inl (not_lt.mp ht)
        have hn : ‖circleMap 0 p.1 p.2‖ = p.1 := by
          simp only [norm_circleMap_zero, abs_of_pos (show 0 < p.1 from hp.1.1)]
        rcases hpr with hpr | hpr
        · simp [hin _ (hne (ne_of_gt (show 0 < p.1 from hp.1.1)) p.2) (by rw [hn]; exact hpr)]
        · simp [hout _ (by rw [hn]; exact hpr.le)]
      _ = ∫ p in Ioc r S ×ˢ Ioo (-Real.pi) Real.pi, P p := by
        apply setIntegral_congr_fun (measurableSet_Ioc.prod measurableSet_Ioo)
        intro p hp
        exact hpolar _ (ne_of_gt (hr.trans hp.1.1)) p.2
      _ = ∫ t in Ioc r S, ∫ θ in Ioo (-Real.pi) Real.pi, P (t, θ) := by
        rw [Measure.volume_eq_prod] at hPint ⊢
        exact setIntegral_prod P hPint
      _ = ∫ t in r..S, ∫ θ in -Real.pi..Real.pi, P (t, θ) := by
        simp_rw [intervalIntegral.integral_of_le hrS,
          intervalIntegral.integral_of_le (neg_le_self Real.pi_pos.le), integral_Ioc_eq_integral_Ioo]
      _ = _ := hpolar_integral hg hr hrS
  have hholzero {q : ℂ → ℂ} {z : ℂ} (hq : DifferentiableAt ℂ q z) :
      dbar q z = 0 := by
    have he := (differentiableAt_complex_iff_differentiableAt_real.mp hq).2
    simp only [smul_eq_mul] at he
    simp [dbar, he, ← mul_assoc, Complex.I_mul_I]
  intro Ω a ha χ hone f hf R hR htarget
  let k : ℂ → ℂ := fun z => (χ z : ℂ)
  have hk : ContDiff ℝ ∞ k := Complex.ofRealCLM.contDiff.comp χ.contDiff
  let g : ℂ → ℂ := fun z => k (a + z) * (z * f (a + z))
  have hshift (z : ℂ) : fderiv ℝ (fun w => k (a + w)) z = fderiv ℝ k (a + z) := by
    have he := ((hk.differentiable (by simp) (a + z)).hasFDerivAt).comp z
      ((hasFDerivAt_const (𝕜 := ℝ) a z).add (hasFDerivAt_id z))
    simpa [Function.comp_def] using he.fderiv
  have hshiftbar (z : ℂ) : dbar (fun w => k (a + w)) z = dbar k (a + z) := by
    simp only [dbar, hshift]
  have hg : ∀ z ≠ 0, ContDiffAt ℝ ∞ g z := by
    intro z hz
    by_cases hs : a + z ∈ tsupport (χ : ℂ → ℝ)
    · have hfa := hf (a + z) ⟨χ.tsupport_subset hs, by simpa using hz⟩
      exact (hk.contDiffAt.comp z (contDiffAt_const.add contDiffAt_id)).mul
        (contDiffAt_id.mul ((hfa.contDiffAt.restrict_scalars ℝ).comp z
          (contDiffAt_const.add contDiffAt_id)))
    · have he : g =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
        filter_upwards [(continuous_const.add continuous_id).continuousAt.eventually
          (notMem_tsupport_iff_eventuallyEq.mp hs)] with w hw
        change χ (a + w) = 0 at hw
        simp [g, k, hw]
      exact contDiffAt_const.congr_of_eventuallyEq he
  have hgbar (z : ℂ) (hz : z ≠ 0) :
      dbar g z = z * (dbar k (a + z) * f (a + z)) := by
    by_cases hs : a + z ∈ tsupport (χ : ℂ → ℝ)
    · have hfa := (hf (a + z) ⟨χ.tsupport_subset hs, by simpa using hz⟩).differentiableAt
      have hH : DifferentiableAt ℂ (fun w => w * f (a + w)) z :=
        differentiableAt_id.mul (hfa.comp z ((differentiableAt_const a).add differentiableAt_id))
      have hK : DifferentiableAt ℝ (fun w => k (a + w)) z :=
        (hk.differentiable (by simp) (a + z)).comp z
          ((differentiableAt_const a).add differentiableAt_id)
      have hprod : dbar g z = dbar (fun w => k (a + w)) z * (z * f (a + z)) +
          k (a + z) * dbar (fun w => w * f (a + w)) z := by
        simp only [g, dbar, fderiv_fun_mul hK (hH.restrictScalars ℝ),
          add_apply, smul_apply, smul_eq_mul]
        ring
      rw [hholzero hH, hshiftbar] at hprod
      simpa only [mul_zero, add_zero, mul_left_comm] using hprod
    · have he : g =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
        filter_upwards [(continuous_const.add continuous_id).continuousAt.eventually
          (notMem_tsupport_iff_eventuallyEq.mp hs)] with w hw
        change χ (a + w) = 0 at hw
        simp [g, k, hw]
      have hk0 : k =ᶠ[𝓝 (a + z)] fun _ => (0 : ℂ) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hs] with w hw
        simp [k, hw]
      simp only [dbar, he.fderiv_eq, hk0.fderiv_eq, fderiv_const_apply,
        zero_apply, mul_zero, zero_add, zero_div, zero_mul]
  have hk_one : k =ᶠ[𝓝 a] fun _ => (1 : ℂ) := by
    filter_upwards [hone] with z hz
    simp [k, hz]
  have hzero_near : ∀ᶠ z in 𝓝 a, dbar k z = 0 := by
    filter_upwards [hk_one.fderiv (𝕜 := ℝ)] with z hz
    simp [dbar, hz]
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp (hone.and hzero_near)
  let r : ℝ := min δ R / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrδ : r < δ := by dsimp [r]; have := min_le_left δ R; linarith
  have hrR : r ≤ R := by dsimp [r]; have := min_le_right δ R; linarith
  have hnear (z : ℂ) (hz : ‖z‖ ≤ r) : χ (a + z) = 1 ∧ dbar k (a + z) = 0 := by
    apply hδsub
    rw [Metric.mem_ball, dist_eq_norm]
    simpa using lt_of_le_of_lt hz hrδ
  obtain ⟨S₀, hS₀, hbound⟩ := χ.hasCompactSupport.isCompact.isBounded.exists_pos_norm_lt
  let S : ℝ := S₀ + ‖a‖ + r + 1
  have hrS : r ≤ S := by dsimp [S]; linarith [norm_nonneg a]
  have hout_supp (z : ℂ) (hz : S ≤ ‖z‖) : a + z ∉ tsupport (χ : ℂ → ℝ) := by
    intro hs
    have hb := hbound (a + z) hs
    have hn : ‖z‖ ≤ ‖a + z‖ + ‖a‖ := by
      simpa using norm_sub_le (a + z) a
    dsimp [S] at hz
    linarith [norm_nonneg a]
  have hin : ∀ z ≠ 0, ‖z‖ ≤ r → dbar g z = 0 := by
    intro z hz hzR
    rw [hgbar z hz, (hnear z hzR).2]
    simp
  have hout : ∀ z, S ≤ ‖z‖ → dbar g z = 0 := by
    intro z hz
    have hs := hout_supp z hz
    have he : g =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
      filter_upwards [(continuous_const.add continuous_id).continuousAt.eventually
        (notMem_tsupport_iff_eventuallyEq.mp hs)] with w hw
      change χ (a + w) = 0 at hw
      simp [g, k, hw]
    simp [dbar, he.fderiv_eq]
  have hI := hannulus hg hr hrS hin hout
  have hrepr (z : ℂ) : z⁻¹ * dbar g z = dbar k (a + z) * f (a + z) := by
    by_cases hz : z = 0
    · subst z
      simp [hk_one.fderiv_eq, dbar]
    · rw [hgbar z hz, ← mul_assoc, inv_mul_cancel₀ hz, one_mul]
  simp_rw [hrepr] at hI
  have houter (θ : ℝ) : g (circleMap 0 S θ) = 0 := by
    have hS : 0 < S := hr.trans_le hrS
    have hz := image_eq_zero_of_notMem_tsupport
      (hout_supp (circleMap 0 S θ) (by simp [norm_circleMap_zero, abs_of_pos hS]))
    simp [g, k, hz]
  have hinner (θ : ℝ) : g (circleMap 0 r θ) =
      circleMap 0 r θ * f (circleMap a r θ) := by
    have hz := (hnear (circleMap 0 r θ) (by simp [norm_circleMap_zero, abs_of_pos hr])).1
    simp only [g, k, hz, Complex.ofReal_one, one_mul]
    congr 1
    congr 1
    simp [circleMap]
  simp_rw [houter, hinner, zero_sub] at hI
  rw [intervalIntegral.integral_neg] at hI
  have hperiod : Function.Periodic
      (fun θ => circleMap 0 r θ * f (circleMap a r θ)) (2 * Real.pi) :=
    (periodic_circleMap 0 r).mul ((periodic_circleMap a r).comp f)
  have hangle : (∫ θ in -Real.pi..Real.pi, circleMap 0 r θ * f (circleMap a r θ)) =
      ∫ θ in 0..2 * Real.pi, circleMap 0 r θ * f (circleMap a r θ) := by
    convert hperiod.intervalIntegral_add_eq (-Real.pi) 0 using 1 <;> congr 1 <;> ring
  have hcircle : circleIntegral f a r = Complex.I *
      (∫ θ in -Real.pi..Real.pi, circleMap 0 r θ * f (circleMap a r θ)) := by
    rw [hangle, ← intervalIntegral.integral_const_mul]
    unfold circleIntegral
    apply intervalIntegral.integral_congr
    intro θ hθ
    simp only [deriv_circleMap, smul_eq_mul]
    ring
  have htrans : (∫ z : ℂ, dbar k (a + z) * f (a + z)) =
      ∫ z : ℂ, dbar k z * f z := by
    exact integral_add_left_eq_self (fun z : ℂ => dbar k z * f z) a
  rw [htrans] at hI
  have hboundary : (∫ z : ℂ, -(2 * Complex.I) * dbar k z * f z) =
      circleIntegral f a r := by
    simp_rw [mul_assoc]
    rw [integral_const_mul, hI, hcircle]
    ring
  have hsmall : Metric.closedBall a R \ Metric.ball a r ⊆ (Ω : Set ℂ) \ {a} := by
    intro z hz
    refine ⟨htarget hz.1, ?_⟩
    intro hza
    have hza' : z = a := hza
    subst z
    exact hz.2 (Metric.mem_ball_self hr)
  have hinvariance : circleIntegral f a R = circleIntegral f a r := by
    apply Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
      hr hrR (s := ∅) Set.countable_empty
    · exact hf.continuousOn.mono hsmall
    · intro z hz
      apply (hf z (hsmall ⟨Metric.ball_subset_closedBall hz.1.1,
        fun hzb => hz.1.2 (Metric.ball_subset_closedBall hzb)⟩)).differentiableAt
  exact hboundary.trans hinvariance.symm

end CanonicalDimensionTwo.LocalDbar
