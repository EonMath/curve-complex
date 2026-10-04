import CurveComplexGenusTwo.Topology.ActualSmoothMorseNormalForm.ActualMorseHessianSymmetry
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.LinearAlgebra.Complex.Determinant

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.OpenPartialHomeomorph.Composition

open scoped ContDiff Topology
open Filter

/-!
Determinant parity from an actual real smooth Morse coordinate system.

Source: J. Milnor, Morse Theory, Annals of Mathematics Studies 51 (1963),
§2, Lemma 2.2, printed p. 6; smoothness and nondegeneracy are defined on p. 4.
The ambient `ℂ` is used only as a two-dimensional REAL inner product space.
The saddle coordinates are ordered positive first, negative second.
-/

/-- The literal quadratic forms required by the caller. The number of negative
square terms is `k.val`. This is the same formula as the caller's private
`morseQuadratic` in `ActualMorseChartGeometry.lean`. -/
def actualComplexMorseQuadratic (k : Fin 3) (w : ℂ) : ℝ :=
  if k = 0 then w.re ^ 2 + w.im ^ 2
  else if k = 1 then w.re ^ 2 - w.im ^ 2
  else -(w.re ^ 2 + w.im ^ 2)

/-- A smooth coordinate system on an open neighborhood of `z₀` inside `U`,
centered at zero, in which the actual function has the literal Morse form.
The open source/target, two inverse identities, and continuity of both maps
are supplied by `OpenPartialHomeomorph`; smoothness is required on BOTH sides.
This predicate describes the OUTPUT of the Morse lemma. -/
structure IsActualComplexSmoothMorseNormalForm
    (f : ℂ → ℝ) (U : Set ℂ) (z₀ : ℂ)
    (k : Fin 3) (e : OpenPartialHomeomorph ℂ ℂ) : Prop where
  center_mem_source : z₀ ∈ e.source
  source_subset : e.source ⊆ U
  center_eq_zero : e z₀ = 0
  contDiffOn : ContDiffOn ℝ ∞ e e.source
  contDiffOn_symm : ContDiffOn ℝ ∞ e.symm e.target
  normal_form : ∀ z ∈ e.source,
    f z = f z₀ + actualComplexMorseQuadratic k (e z)

private theorem square_second (a : ℂ → ℝ) (z : ℂ)
    (ha : ContDiffAt ℝ 2 a z) (ha0 : a z = 0) (v w : ℂ) :
    fderiv ℝ (fderiv ℝ (fun x => a x * a x)) z v w =
      2 * (fderiv ℝ a z v) * (fderiv ℝ a z w) := by
  have hd := (ha.differentiableAt (by norm_num)).hasFDerivAt
  have hdd := (ha.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt
    (by norm_num)
  have heq : fderiv ℝ (fun x => a x * a x) =ᶠ[𝓝 z]
      fun x => a x • fderiv ℝ a x + a x • fderiv ℝ a x := by
    filter_upwards [ha.eventually (by norm_num)] with x hx
    exact (hx.differentiableAt (by norm_num)).hasFDerivAt.fun_mul
      (hx.differentiableAt (by norm_num)).hasFDerivAt |>.fderiv
  have hh := ((hd.fun_smul hdd.hasFDerivAt).fun_add (hd.fun_smul hdd.hasFDerivAt)).fderiv
  rw [heq.fderiv_eq, hh]
  simp only [ha0, zero_smul, zero_add, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

private theorem signed_squares_second (a b : ℂ → ℝ) (z : ℂ) (c s t : ℝ)
    (ha : ContDiffAt ℝ 2 a z) (hb : ContDiffAt ℝ 2 b z)
    (ha0 : a z = 0) (hb0 : b z = 0) (v w : ℂ) :
    fderiv ℝ (fderiv ℝ (fun x => c + s * (a x * a x) + t * (b x * b x))) z v w =
      s * (2 * (fderiv ℝ a z v) * (fderiv ℝ a z w)) +
      t * (2 * (fderiv ℝ b z v) * (fderiv ℝ b z w)) := by
  have ha' := ha.mul ha
  have hb' := hb.mul hb
  have heq : fderiv ℝ (fun x => c + s * (a x * a x) + t * (b x * b x)) =ᶠ[𝓝 z]
      fun x => s • fderiv ℝ (fun x => a x * a x) x +
        t • fderiv ℝ (fun x => b x * b x) x := by
    filter_upwards [ha'.eventually (by norm_num), hb'.eventually (by norm_num)] with x hx hy
    simpa only [Pi.add_apply] using (((hx.differentiableAt (by norm_num)).hasFDerivAt.const_mul s).const_add c).fun_add
      ((hy.differentiableAt (by norm_num)).hasFDerivAt.const_mul t) |>.fderiv
  have ha'' := (ha'.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt
    (by norm_num)
  have hb'' := (hb'.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt
    (by norm_num)
  have hh := ((ha''.hasFDerivAt.fun_const_smul s).fun_add (hb''.hasFDerivAt.fun_const_smul t)).fderiv
  rw [heq.fderiv_eq, hh]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    square_second a z ha ha0 v w, square_second b z hb hb0 v w]

private theorem complex_linear_det (T : ℂ →L[ℝ] ℂ) :
    T.det = (T 1).re * (T Complex.I).im - (T Complex.I).re * (T 1).im := by
  have hm : T.toLinearMap.toMatrix Complex.basisOneI Complex.basisOneI =
      !![(T 1).re, (T Complex.I).re; (T 1).im, (T Complex.I).im] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr, Complex.coe_basisOneI]
  change T.toLinearMap.det = _
  rw [← LinearMap.det_toMatrix Complex.basisOneI, hm, Matrix.det_fin_two_of]

private theorem signed_squares_det (e : ℂ → ℂ) (z : ℂ) (c s t : ℝ)
    (he : ContDiffAt ℝ 2 e z) (he0 : e z = 0) :
    (fderiv ℝ (gradient (fun x => c + s * ((e x).re * (e x).re) +
      t * ((e x).im * (e x).im))) z).det = 4 * s * t * (fderiv ℝ e z).det ^ 2 := by
  let a : ℂ → ℝ := fun x => (e x).re
  let b : ℂ → ℝ := fun x => (e x).im
  have ha : ContDiffAt ℝ 2 a z := Complex.reCLM.contDiff.contDiffAt.comp z he
  have hb : ContDiffAt ℝ 2 b z := Complex.imCLM.contDiff.contDiffAt.comp z he
  have ha0 : a z = 0 := by simp [a, he0]
  have hb0 : b z = 0 := by simp [b, he0]
  have hda : ∀ v, fderiv ℝ a z v = (fderiv ℝ e z v).re := by
    intro v
    change (fderiv ℝ (Complex.reCLM ∘ e) z) v = _
    rw [(Complex.reCLM.hasFDerivAt.comp z
      (he.differentiableAt (by norm_num)).hasFDerivAt).fderiv]
    rfl
  have hdb : ∀ v, fderiv ℝ b z v = (fderiv ℝ e z v).im := by
    intro v
    change (fderiv ℝ (Complex.imCLM ∘ e) z) v = _
    rw [(Complex.imCLM.hasFDerivAt.comp z
      (he.differentiableAt (by norm_num)).hasFDerivAt).fderiv]
    rfl
  let g : ℂ → ℝ := fun x => c + s * (a x * a x) + t * (b x * b x)
  have hg : ContDiffAt ℝ 2 g z :=
    ((contDiffAt_const.add (contDiffAt_const.mul (ha.mul ha))).add
      (contDiffAt_const.mul (hb.mul hb)))
  have hh : ∀ v w : ℂ, inner ℝ (fderiv ℝ (gradient g) z v) w =
      s * (2 * (fderiv ℝ e z v).re * (fderiv ℝ e z w).re) +
      t * (2 * (fderiv ℝ e z v).im * (fderiv ℝ e z w).im) := by
    intro v w
    rw [actual_complex_scalar_gradient_derivative_pairing g z hg]
    exact (signed_squares_second a b z c s t ha hb ha0 hb0 v w).trans (by rw [hda, hda, hdb, hdb])
  have h11 := hh 1 1
  have h12 := hh 1 Complex.I
  have h21 := hh Complex.I 1
  have h22 := hh Complex.I Complex.I
  simp only [Complex.inner, one_mul, Complex.conj_re, Complex.I_mul_re,
    Complex.conj_im, neg_neg] at h11 h12 h21 h22
  change (fderiv ℝ (gradient g) z).det = _
  rw [complex_linear_det, complex_linear_det, h11, h12, h21, h22]
  ring

private theorem smooth_inverse_det_ne_zero
    (e : OpenPartialHomeomorph ℂ ℂ) (z : ℂ) (hz : z ∈ e.source)
    (he : ContDiffOn ℝ ∞ e e.source) (hei : ContDiffOn ℝ ∞ e.symm e.target) :
    (fderiv ℝ e z).det ≠ 0 := by
  have hd := ((he z hz).contDiffAt (e.open_source.mem_nhds hz)).differentiableAt (by simp)
  have hdi := ((hei (e z) (e.map_source hz)).contDiffAt
    (e.open_target.mem_nhds (e.map_source hz))).differentiableAt (by simp)
  have hi : (e.symm ∘ e) =ᶠ[𝓝 z] id := by
    filter_upwards [e.open_source.mem_nhds hz] with x hx
    exact e.left_inv hx
  have hcomp : (fderiv ℝ e.symm (e z)).comp (fderiv ℝ e z) = ContinuousLinearMap.id ℝ ℂ := by
    rw [← (hdi.hasFDerivAt.comp z hd.hasFDerivAt).fderiv, hi.fderiv_eq, fderiv_id]
  have hdet := congrArg (fun T : ℂ →L[ℝ] ℂ => T.toLinearMap.det) hcomp
  change ((fderiv ℝ e.symm (e z)).toLinearMap.comp (fderiv ℝ e z).toLinearMap).det = _ at hdet
  rw [LinearMap.det_comp] at hdet
  change _ * _ = (LinearMap.id : ℂ →ₗ[ℝ] ℂ).det at hdet
  rw [LinearMap.det_id] at hdet
  intro hzero
  change (fderiv ℝ e z).toLinearMap.det = 0 at hzero
  rw [hzero, mul_zero] at hdet
  norm_num at hdet

/-- A separate consequence of a smooth Morse coordinate system.

Milnor's coordinate-Hessian calculation in the proof of Lemma 2.2 (p. 6)
and the critical-point coordinate invariance of the Hessian (pp. 4–5) give
the determinant transformation. The factor `4` is literal in dimension two
because the Hessian of each signed square has diagonal entry `±2`.
The determinant/parity equation is an OUTPUT consequence, never an input to
`actual_complex_smooth_morse_normal_form`. -/
theorem actual_complex_smooth_morse_normal_form_det_parity
    (f : ℂ → ℝ) (U : Set ℂ) (z₀ : ℂ)
    (k : Fin 3) (e : OpenPartialHomeomorph ℂ ℂ)
    (hform : IsActualComplexSmoothMorseNormalForm f U z₀ k e) :
    (fderiv ℝ e z₀).det ≠ 0 ∧
      (fderiv ℝ (gradient f) z₀).det =
        4 * (-1 : ℝ) ^ k.val * ((fderiv ℝ e z₀).det) ^ 2 ∧
      (if 0 < (fderiv ℝ (gradient f) z₀).det then (1 : ℤ) else -1) =
        (-1 : ℤ) ^ k.val := by
  have he : ContDiffAt ℝ 2 e z₀ :=
    ((hform.contDiffOn z₀ hform.center_mem_source).contDiffAt
      (e.open_source.mem_nhds hform.center_mem_source)).of_le (by simp)
  have hn := smooth_inverse_det_ne_zero e z₀ hform.center_mem_source
    hform.contDiffOn hform.contDiffOn_symm
  have hdet (s t : ℝ)
      (hq : ∀ w : ℂ, actualComplexMorseQuadratic k w =
        s * (w.re * w.re) + t * (w.im * w.im)) :
      (fderiv ℝ (gradient f) z₀).det = 4 * s * t * (fderiv ℝ e z₀).det ^ 2 := by
    have heq : f =ᶠ[𝓝 z₀] fun x => f z₀ + s * ((e x).re * (e x).re) +
        t * ((e x).im * (e x).im) := by
      filter_upwards [e.open_source.mem_nhds hform.center_mem_source] with x hx
      rw [hform.normal_form x hx, hq]
      ring
    rw [heq.gradient.fderiv_eq]
    exact signed_squares_det e z₀ (f z₀) s t he hform.center_eq_zero
  refine ⟨hn, ?_, ?_⟩
  · fin_cases k
    · simpa using hdet 1 1 (by intro w; simp [actualComplexMorseQuadratic, pow_two])
    · simpa using hdet 1 (-1) (by intro w; simp [actualComplexMorseQuadratic, pow_two, sub_eq_add_neg])
    · simpa using hdet (-1) (-1) (by intro w; simp [actualComplexMorseQuadratic, pow_two, add_comm])
  · have hpos : 0 < (fderiv ℝ e z₀).det ^ 2 := sq_pos_of_ne_zero hn
    fin_cases k
    · have hh := hdet 1 1 (by intro w; simp [actualComplexMorseQuadratic, pow_two])
      have hhpos : 0 < (fderiv ℝ (gradient f) z₀).det := by rw [hh]; positivity
      simp [hhpos]
    · have hh := hdet 1 (-1) (by intro w; simp [actualComplexMorseQuadratic, pow_two, sub_eq_add_neg])
      have hhneg : ¬ 0 < (fderiv ℝ (gradient f) z₀).det := by rw [hh]; nlinarith
      simp [hhneg]
    · have hh := hdet (-1) (-1) (by intro w; simp [actualComplexMorseQuadratic, pow_two, add_comm])
      have hhpos : 0 < (fderiv ℝ (gradient f) z₀).det := by rw [hh]; nlinarith
      simp [hhpos]
