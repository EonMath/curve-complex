import CurveComplexGenusTwo.Topology.ActualSmoothMorseNormalForm.ActualComplexSmoothMorseParity
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Analysis.Normed.Module.FiniteDimension

open scoped ContDiff Topology
open Filter Set

private theorem local_coordinates
    (g : ℂ → ℂ) (V : Set ℂ) (hV : IsOpen V) (h0 : (0 : ℂ) ∈ V)
    (hg : ContDiffOn ℝ ∞ g V) (hd : (fderiv ℝ g 0).det ≠ 0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      (0 : ℂ) ∈ e.source ∧ e.source ⊆ V ∧ (e : ℂ → ℂ) = g ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  have hg0 : ContDiffAt ℝ ∞ g 0 := (hg 0 h0).contDiffAt (hV.mem_nhds h0)
  have hd0 : HasFDerivAt g (fderiv ℝ g 0) 0 := (hg0.differentiableAt (by simp)).hasFDerivAt
  let D := (fderiv ℝ g 0).toContinuousLinearEquivOfDetNeZero hd
  have hD : HasFDerivAt g D.toContinuousLinearMap 0 := by simpa [D] using hd0
  let e0 := hg0.toOpenPartialHomeomorph g hD (by simp)
  have he0 : (0 : ℂ) ∈ e0.source := hg0.mem_toOpenPartialHomeomorph_source hD (by simp)
  have hdc : ContinuousAt (fun z => (fderiv ℝ g z).det) 0 :=
    ContinuousLinearMap.continuous_det.continuousAt.comp
      (hg0.fderiv_right (m := ∞) (by simp)).continuousAt
  obtain ⟨W, hWsub, hWopen, hW0⟩ := mem_nhds_iff.mp
    (inter_mem (hV.mem_nhds h0) (hdc.eventually_ne hd))
  let e := e0.restrOpen W hWopen
  have hsub : e.source ⊆ V := fun z hz => (hWsub hz.2).1
  have heq : (e : ℂ → ℂ) = g := rfl
  have hes : ContDiffOn ℝ ∞ e e.source := by rw [heq]; exact hg.mono hsub
  refine ⟨e, ⟨he0, hW0⟩, hsub, heq, hes, ?_⟩
  intro y hy
  have hx := e.map_target hy
  have hdx : (fderiv ℝ g (e.symm y)).det ≠ 0 := (hWsub hx.2).2
  have hgs : ContDiffAt ℝ ∞ e (e.symm y) :=
    (hes _ hx).contDiffAt (e.open_source.mem_nhds hx)
  have hde : HasFDerivAt e
      ((fderiv ℝ g (e.symm y)).toContinuousLinearEquivOfDetNeZero hdx).toContinuousLinearMap
      (e.symm y) := by
    simpa only [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero, heq]
      using hgs.differentiableAt (by simp) |>.hasFDerivAt
  exact (e.contDiffAt_symm hy hde hgs).contDiffWithinAt

private theorem plane_det (T : ℂ →L[ℝ] ℂ) :
    T.det = (T 1).re * (T Complex.I).im - (T Complex.I).re * (T 1).im := by
  have hm : T.toLinearMap.toMatrix Complex.basisOneI Complex.basisOneI =
      !![(T 1).re, (T Complex.I).re; (T 1).im, (T Complex.I).im] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr, Complex.coe_basisOneI]
  change T.toLinearMap.det = _
  rw [← LinearMap.det_toMatrix Complex.basisOneI, hm, Matrix.det_fin_two_of]

private noncomputable def swapPlane : ℂ →L[ℝ] ℂ :=
  Complex.imCLM.smulRight 1 + Complex.reCLM.smulRight Complex.I

private theorem swapPlane_re (z : ℂ) : (swapPlane z).re = z.im := by
  simp [swapPlane, Complex.real_smul]
private theorem swapPlane_im (z : ℂ) : (swapPlane z).im = z.re := by
  simp [swapPlane, Complex.real_smul]

private theorem normal_form_from_map
    (f : ℂ → ℝ) (g : ℂ → ℂ) (U : Set ℂ) (k : Fin 3)
    (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (hg : ContDiffOn ℝ ∞ g U) (hg0 : g 0 = 0)
    (hd : (fderiv ℝ g 0).det ≠ 0)
    (hq : ∀ z ∈ U, f z = f 0 + actualComplexMorseQuadratic k (g z)) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, IsActualComplexSmoothMorseNormalForm f U 0 k e := by
  obtain ⟨e, he0, heU, heq, he, hei⟩ := local_coordinates g U hU h0 hg hd
  refine ⟨e, he0, heU, ?_, he, hei, ?_⟩
  · simpa only [heq] using hg0
  · intro z hz
    simpa only [heq] using hq z (heU hz)

private theorem signed_coordinate_form
    (g : ℂ → ℂ) (U : Set ℂ) (s t : ℝ)
    (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (hg : ContDiffOn ℝ ∞ g U) (hg0 : g 0 = 0)
    (hd : (fderiv ℝ g 0).det ≠ 0)
    (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    ∃ (k : Fin 3) (e : OpenPartialHomeomorph ℂ ℂ),
      IsActualComplexSmoothMorseNormalForm
        (fun z => s * (g z).re ^ 2 + t * (g z).im ^ 2) U 0 k e := by
  have hbase (k : Fin 3) (hq : ∀ z ∈ U,
      s * (g z).re ^ 2 + t * (g z).im ^ 2 = actualComplexMorseQuadratic k (g z)) :
      ∃ e, IsActualComplexSmoothMorseNormalForm
        (fun z => s * (g z).re ^ 2 + t * (g z).im ^ 2) U 0 k e := by
    apply normal_form_from_map _ g U k hU h0 hg hg0 hd
    intro z hz
    simpa only [hg0, Complex.zero_re, Complex.zero_im, zero_pow (by decide : 2 ≠ 0),
      mul_zero, zero_add] using hq z hz
  rcases hs with rfl | rfl
  · rcases ht with rfl | rfl
    · obtain ⟨e, he⟩ := hbase 0 (by intro z hz; simp [actualComplexMorseQuadratic])
      exact ⟨0, e, he⟩
    · obtain ⟨e, he⟩ := hbase 1 (by intro z hz; simp [actualComplexMorseQuadratic, sub_eq_add_neg])
      exact ⟨1, e, he⟩
  · rcases ht with rfl | rfl
    · have hsg : ContDiffOn ℝ ∞ (fun z => swapPlane (g z)) U :=
        swapPlane.contDiff.comp_contDiffOn hg
      have hs0 : swapPlane (g 0) = 0 := by simp [hg0]
      have hsd : (fderiv ℝ (fun z => swapPlane (g z)) 0).det ≠ 0 := by
        have hder := swapPlane.hasFDerivAt.comp 0
          (((hg 0 h0).contDiffAt (hU.mem_nhds h0)).differentiableAt (by simp)).hasFDerivAt
        change (fderiv ℝ (swapPlane ∘ g) 0).det ≠ 0
        rw [hder.fderiv, plane_det]
        rw [plane_det] at hd
        simpa [ContinuousLinearMap.comp_apply, swapPlane_re, swapPlane_im, mul_comm, neg_sub] using neg_ne_zero.mpr hd
      obtain ⟨e, he⟩ := normal_form_from_map
        (fun z => (-1 : ℝ) * (g z).re ^ 2 + 1 * (g z).im ^ 2)
        (fun z => swapPlane (g z)) U 1 hU h0 hsg hs0 hsd (by
          intro z hz
          simp [actualComplexMorseQuadratic, hg0, swapPlane_re, swapPlane_im]
          ring)
      exact ⟨1, e, he⟩
    · obtain ⟨e, he⟩ := hbase 2 (by intro z hz; simp [actualComplexMorseQuadratic, add_comm])
      exact ⟨2, e, he⟩

private theorem shear_coordinate_det (u v j : ℂ → ℝ) (t : ℝ)
    (hu : ContDiffAt ℝ ∞ u 0) (hv : ContDiffAt ℝ ∞ v 0)
    (hj : ContDiffAt ℝ ∞ j 0) :
    (fderiv ℝ (fun z : ℂ =>
      (u z * (z.re + j z * (z.im - t * z.re))) • (1 : ℂ) +
      (v z * (z.im - t * z.re)) • Complex.I) 0).det = u 0 * v 0 := by
  let Y : ℂ →L[ℝ] ℝ := Complex.imCLM - t • Complex.reCLM
  have hY : HasFDerivAt (fun z : ℂ => z.im - t * z.re) Y 0 := by
    simpa only [Y, smul_eq_mul, Complex.imCLM_apply, Complex.reCLM_apply] using Complex.imCLM.hasFDerivAt.fun_sub
      (Complex.reCLM.hasFDerivAt.fun_const_smul t)
  have hjY := ((hj.differentiableAt (by simp)).hasFDerivAt.fun_mul hY)
  have hX := Complex.reCLM.hasFDerivAt.fun_add hjY
  have hux := (hu.differentiableAt (by simp)).hasFDerivAt.fun_mul hX
  have hvy := (hv.differentiableAt (by simp)).hasFDerivAt.fun_mul hY
  have hder := (hux.smul_const (1 : ℂ)).fun_add (hvy.smul_const Complex.I)
  simp only [Complex.reCLM_apply] at hder
  rw [hder.fderiv, plane_det]
  simp [Y, Complex.real_smul, smul_apply, add_apply, sub_apply,
    ContinuousLinearMap.smulRight_apply, Complex.mul_re, Complex.mul_im]
  ring

/-- Proposed leaf, awaiting source review. The smooth completing-squares step
of Milnor's proof of Lemma 2.2, p. 7, specialized to two real dimensions. -/
theorem actual_complex_smooth_quadratic_coefficients_normal_form
    (a b c : ℂ → ℝ) (U : Set ℂ) (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hc : ContDiffOn ℝ ∞ c U)
    (hdet : a 0 * c 0 - (b 0) ^ 2 ≠ 0) :
    ∃ (k : Fin 3) (e : OpenPartialHomeomorph ℂ ℂ),
      IsActualComplexSmoothMorseNormalForm
        (fun z => a z * z.re ^ 2 + 2 * b z * z.re * z.im + c z * z.im ^ 2)
        U 0 k e := by
  obtain ⟨t, hpivot⟩ : ∃ t : ℝ, a 0 + 2 * t * b 0 + t ^ 2 * c 0 ≠ 0 := by
    by_cases ha0 : a 0 = 0
    · by_cases hplus : a 0 + 2 * b 0 + c 0 = 0
      · refine ⟨-1, ?_⟩
        intro hminus
        have hb0 : b 0 = 0 := by norm_num at hminus; linarith
        exact hdet (by rw [ha0, hb0]; ring)
      · refine ⟨1, ?_⟩
        simpa using hplus
    · exact ⟨0, by simpa using ha0⟩
  let A : ℂ → ℝ := fun z => a z + 2 * t * b z + t ^ 2 * c z
  let B : ℂ → ℝ := fun z => b z + t * c z
  let d : ℂ → ℝ := fun z => c z - B z ^ 2 / A z
  have hA : ContDiffOn ℝ ∞ A U := (ha.add (contDiffOn_const.mul hb)).add (contDiffOn_const.mul hc)
  have hB : ContDiffOn ℝ ∞ B U := hb.add (contDiffOn_const.mul hc)
  have hA0 : A 0 ≠ 0 := hpivot
  have hdet' : A 0 * c 0 - B 0 ^ 2 ≠ 0 := by
    convert hdet using 1 <;> dsimp [A, B] <;> ring
  have hd0 : d 0 ≠ 0 := by
    intro hz
    apply hdet'
    dsimp [d] at hz
    field_simp at hz
    nlinarith
  have hAc : ContinuousAt A 0 := ((hA 0 h0).contDiffAt (hU.mem_nhds h0)).continuousAt
  have hdc : ContinuousAt d 0 := by
    exact ((hc 0 h0).contDiffAt (hU.mem_nhds h0)).continuousAt.sub
      ((((hB 0 h0).contDiffAt (hU.mem_nhds h0)).continuousAt.pow 2).div hAc hA0)
  obtain ⟨s, hs, hsA⟩ : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ 0 < s * A 0 := by
    rcases lt_or_gt_of_ne hA0 with hh | hh
    · exact ⟨-1, Or.inr rfl, by linarith⟩
    · exact ⟨1, Or.inl rfl, by simpa using hh⟩
  obtain ⟨q, hq, hqd⟩ : ∃ q : ℝ, (q = 1 ∨ q = -1) ∧ 0 < q * d 0 := by
    rcases lt_or_gt_of_ne hd0 with hh | hh
    · exact ⟨-1, Or.inr rfl, by linarith⟩
    · exact ⟨1, Or.inl rfl, by simpa using hh⟩
  have hAn : ∀ᶠ z in 𝓝 (0 : ℂ), 0 < s * A z := (hAc.const_mul s).eventually (eventually_gt_nhds hsA)
  have hdn : ∀ᶠ z in 𝓝 (0 : ℂ), 0 < q * d z := (hdc.const_mul q).eventually (eventually_gt_nhds hqd)
  obtain ⟨V, hVsub, hVopen, hV0⟩ := mem_nhds_iff.mp (inter_mem (hU.mem_nhds h0) (inter_mem hAn hdn))
  have hVU : V ⊆ U := fun z hz => (hVsub hz).1
  have hAval : ∀ z ∈ V, A z ≠ 0 := by
    intro z hz hzero
    have hh : 0 < s * A z := (hVsub hz).2.1
    rw [hzero, mul_zero] at hh
    exact lt_irrefl 0 hh
  have hd : ContDiffOn ℝ ∞ d V :=
    (hc.mono hVU).sub (((hB.mono hVU).pow 2).div (hA.mono hVU) hAval)
  let u : ℂ → ℝ := fun z => Real.sqrt (s * A z)
  let v : ℂ → ℝ := fun z => Real.sqrt (q * d z)
  let j : ℂ → ℝ := fun z => B z / A z
  have hu : ContDiffOn ℝ ∞ u V := (contDiffOn_const.mul (hA.mono hVU)).sqrt
    (fun z hz => ne_of_gt (hVsub hz).2.1)
  have hv : ContDiffOn ℝ ∞ v V := (contDiffOn_const.mul hd).sqrt
    (fun z hz => ne_of_gt (hVsub hz).2.2)
  have hj : ContDiffOn ℝ ∞ j V := (hB.mono hVU).div (hA.mono hVU) hAval
  let g : ℂ → ℂ := fun z =>
    (u z * (z.re + j z * (z.im - t * z.re))) • (1 : ℂ) +
    (v z * (z.im - t * z.re)) • Complex.I
  have hre : ContDiffOn ℝ ∞ (fun z : ℂ => z.re) V := Complex.reCLM.contDiff.contDiffOn
  have him : ContDiffOn ℝ ∞ (fun z : ℂ => z.im) V := Complex.imCLM.contDiff.contDiffOn
  have hg : ContDiffOn ℝ ∞ g V :=
    ((hu.mul (hre.add (hj.mul (him.sub (contDiffOn_const.mul hre))))).smul contDiffOn_const).add
      ((hv.mul (him.sub (contDiffOn_const.mul hre))).smul contDiffOn_const)
  have hg0 : g 0 = 0 := by simp [g]
  have hgd : (fderiv ℝ g 0).det ≠ 0 := by
    rw [shear_coordinate_det u v j t
      ((hu 0 hV0).contDiffAt (hVopen.mem_nhds hV0))
      ((hv 0 hV0).contDiffAt (hVopen.mem_nhds hV0))
      ((hj 0 hV0).contDiffAt (hVopen.mem_nhds hV0))]
    exact mul_ne_zero (ne_of_gt (Real.sqrt_pos.2 hsA)) (ne_of_gt (Real.sqrt_pos.2 hqd))
  have hidentity : ∀ z ∈ V,
      a z * z.re ^ 2 + 2 * b z * z.re * z.im + c z * z.im ^ 2 =
        s * (g z).re ^ 2 + q * (g z).im ^ 2 := by
    intro z hz
    have hu2 : u z ^ 2 = s * A z := Real.sq_sqrt (le_of_lt (hVsub hz).2.1)
    have hv2 : v z ^ 2 = q * d z := Real.sq_sqrt (le_of_lt (hVsub hz).2.2)
    have hs2 : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
    have hq2 : q ^ 2 = 1 := by rcases hq with rfl | rfl <;> norm_num
    have hgr : (g z).re = u z * (z.re + j z * (z.im - t * z.re)) := by simp [g, Complex.real_smul]
    have hgi : (g z).im = v z * (z.im - t * z.re) := by simp [g, Complex.real_smul]
    rw [hgr, hgi, mul_pow, mul_pow, hu2, hv2]
    calc
      _ = A z * (z.re + j z * (z.im - t * z.re)) ^ 2 + d z * (z.im - t * z.re) ^ 2 := by
        dsimp [j, d]
        field_simp [hAval z hz]
        dsimp [A, B]
        ring
      _ = _ := by rcases hs with rfl | rfl <;> rcases hq with rfl | rfl <;> ring
  obtain ⟨k, e, he⟩ := signed_coordinate_form g V s q hVopen hV0 hg hg0 hgd hs hq
  refine ⟨k, e, he.center_mem_source, he.source_subset.trans hVU, he.center_eq_zero,
    he.contDiffOn, he.contDiffOn_symm, ?_⟩
  intro z hz
  rw [hidentity z (he.source_subset hz), he.normal_form z hz]
  simp [hg0]
