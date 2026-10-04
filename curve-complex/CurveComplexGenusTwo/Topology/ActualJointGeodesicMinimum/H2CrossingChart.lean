import CurveComplexGenusTwo.Topology.ActualJointGeodesicMinimum.Providers
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.OriginalLoopDefinitions
import CurveComplexGenusTwo.Foundations.FoundationsIntersectionPort
import CurveComplexGenusTwo.Dictionary.Genus
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Homotopy.Lifting

namespace CurveComplex.Hyperbolic.JointMinimum

open Set Topology CurveComplex.LocalSurgery
open scoped Manifold UpperHalfPlane
open Matrix
open scoped MatrixGroups

private theorem sl_stabilizer_maps_vertical_one (z : H2)
    (h : dist UpperHalfPlane.I z = 1) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      (A • UpperHalfPlane.I : H2) = UpperHalfPlane.I ∧
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
      · simpa [verticalPath,b] using hpole.2
      · simpa [verticalPath] using him
    let S : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
      Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) ModularGroup.S
    refine ⟨S,?_,?_⟩
    · have hzero : verticalPath 0 = UpperHalfPlane.I := by
        apply UpperHalfPlane.ext_re_im <;> simp [verticalPath]
      rw [←hzero]
      have hh := modular_S_verticalPath 0
      change (S • verticalPath 0 : H2) = verticalPath (-0) at hh
      simpa only [neg_zero] using hh
    · rw [hz]
      exact modular_S_verticalPath 1
  · have hab : 0 < a^2+b^2 := by
      by_contra hn
      have ha : a=0 := by nlinarith [sq_nonneg a,sq_nonneg b]
      have hb : b=0 := by nlinarith [sq_nonneg a,sq_nonneg b]
      exact hpole ⟨ha,hb⟩
    exact ⟨stabilizerRotation a b hab,stabilizerRotation_fixes_I a b hab,
      stabilizerRotation_maps_vertical_one z h hab⟩

private theorem sl_maps_ordered_unit_pair (x y : H2)
    (hxy : dist x y = 1) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      (A • UpperHalfPlane.I : H2) = x ∧
      (A • verticalPath 1 : H2) = y := by
  let A₀ := x.toSL2R
  let e₀ : H2 ≃ᵢ H2 := IsometryEquiv.constSMul A₀
  have he₀ : e₀ UpperHalfPlane.I = x := x.toSL2R_smul_I
  let w : H2 := e₀.symm y
  have hw : dist UpperHalfPlane.I w = 1 := by
    have hdist := e₀.isometry.dist_eq UpperHalfPlane.I (e₀.symm y)
    rw [e₀.apply_symm_apply,he₀] at hdist
    simpa [w,hxy] using hdist.symm
  obtain ⟨A,hAI,hAV⟩ := sl_stabilizer_maps_vertical_one w hw
  refine ⟨A₀*A,?_,?_⟩
  · rw [mul_smul,hAI]
    exact x.toSL2R_smul_I
  · rw [mul_smul,hAV]
    exact e₀.apply_symm_apply y

private theorem isometric_line_is_sl_axis (f : ℝ → H2) (hf : Isometry f) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∀ t : ℝ, f t = A • verticalPath t := by
  have h01 : dist (f 0) (f 1) = 1 := by
    simpa using hf.dist_eq 0 1
  obtain ⟨A,hA0,hA1⟩ := sl_maps_ordered_unit_pair (f 0) (f 1) h01
  let e : H2 ≃ᵢ H2 := IsometryEquiv.constSMul A
  have hnorm : Isometry (fun t : ℝ => e.symm (f t)) := e.symm.isometry.comp hf
  have hzero : verticalPath 0 = UpperHalfPlane.I := by
    apply UpperHalfPlane.ext_re_im <;> simp [verticalPath]
  have hnorm0 : e.symm (f 0) = verticalPath 0 := by
    rw [←hA0]
    change e.symm (e UpperHalfPlane.I) = verticalPath 0
    rw [e.symm_apply_apply,←hzero]
  have hnorm1 : e.symm (f 1) = verticalPath 1 := by
    rw [←hA1]
    change e.symm (e (verticalPath 1)) = verticalPath 1
    rw [e.symm_apply_apply]
  have hv := isometry_eq_vertical_of_values _ hnorm hnorm0 hnorm1
  refine ⟨A,?_⟩
  intro t
  apply e.symm.injective
  change e.symm (f t) = e.symm (e (verticalPath t))
  rw [e.symm_apply_apply]
  exact hv t

private theorem mem_vertical_range (w : H2) :
    w ∈ Set.range verticalPath ↔ w.re = 0 := by
  constructor
  · rintro ⟨t, rfl⟩
    rfl
  · intro h
    refine ⟨Real.log w.im, ?_⟩
    apply UpperHalfPlane.ext_re_im
    · simpa [verticalPath] using h.symm
    · simp [verticalPath, Real.exp_log w.im_pos]

private theorem sl_re_zero_iff (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (w : H2) :
    (A • w : H2).re = 0 ↔
      A 0 0 * A 1 0 * (w.re ^ 2 + w.im ^ 2) +
        (A 0 0 * A 1 1 + A 0 1 * A 1 0) * w.re + A 0 1 * A 1 1 = 0 := by
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using A.property
  have hden : 0 < (A 1 0 * w.re + A 1 1)^2 + (A 1 0 * w.im)^2 := by
    by_contra hn
    have h1 : A 1 0 * w.im = 0 := by
      nlinarith [sq_nonneg (A 1 0 * w.re + A 1 1), sq_nonneg (A 1 0 * w.im)]
    have hc : A 1 0 = 0 := (mul_eq_zero.mp h1).resolve_right w.im_ne_zero
    rw [hc] at hn hdet
    norm_num at hn hdet
    rw [hn, mul_zero] at hdet
    norm_num at hdet
  change ((A • w : H2) : ℂ).re = 0 ↔ _
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [Complex.div_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.add_im,
    Complex.mul_im, add_zero, Complex.normSq_apply, Algebra.algebraMap_self,
    RingHom.id_apply]
  simp only [UpperHalfPlane.re, UpperHalfPlane.im] at hden ⊢
  rw [← add_div]
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · nlinarith only [h]
    · exact (hden.ne' (by simpa only [pow_two] using h)).elim
  · intro h
    left
    nlinarith only [h]

private def parabolaRegion (c d : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1^2 + c*p.1+d < p.2}

private noncomputable def parabolaCoordinates (c d : ℝ) :
    H2 ≃ₜ parabolaRegion c d where
  toFun w := ⟨(w.re, w.re^2+w.im^2+c*w.re+d), by
    dsimp [parabolaRegion]
    nlinarith [sq_pos_of_pos w.im_pos]⟩
  invFun p := UpperHalfPlane.mk
    ⟨p.val.1, Real.sqrt (p.val.2-p.val.1^2-c*p.val.1-d)⟩
    (Real.sqrt_pos.mpr (by have := p.property; dsimp [parabolaRegion] at this; linarith))
  left_inv w := by
    apply UpperHalfPlane.ext_re_im
    · rfl
    · dsimp
      rw [show w.re^2+w.im^2+c*w.re+d-w.re^2-c*w.re-d = w.im^2 by ring]
      exact Real.sqrt_sq w.im_pos.le
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · dsimp
      rw [Real.sq_sqrt (by have := p.property; dsimp [parabolaRegion] at this; linarith)]
      ring
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact UpperHalfPlane.continuous_re.prodMk
      ((((UpperHalfPlane.continuous_re.pow 2).add (UpperHalfPlane.continuous_im.pow 2)).add
        (continuous_const.mul UpperHalfPlane.continuous_re)).add continuous_const)
  continuous_invFun := by
    apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
    change Continuous (fun p : parabolaRegion c d =>
      (⟨p.val.1, Real.sqrt (p.val.2-p.val.1^2-c*p.val.1-d)⟩ : ℂ))
    have heq : (fun p : parabolaRegion c d =>
      (⟨p.val.1, Real.sqrt (p.val.2-p.val.1^2-c*p.val.1-d)⟩ : ℂ)) =
        (fun p => (p.val.1 : ℂ) + (Real.sqrt (p.val.2-p.val.1^2-c*p.val.1-d) : ℂ)*Complex.I) := by
      funext p
      apply Complex.ext <;> simp
    rw [heq]
    fun_prop

theorem distinct_h2_isometric_lines_have_crossing_chart
    (f g : ℝ → H2) (hf : Isometry f) (hg : Isometry g)
    (hne : Set.range f ≠ Set.range g)
    (z : H2) (hz : z ∈ Set.range f ∩ Set.range g) :
    ∃ (U : Set H2) (V : Set (ℝ × ℝ)) (hU : z ∈ U) (h : U ≃ₜ V),
      IsOpen U ∧ IsOpen V ∧
      ((h ⟨z, hU⟩ : V) : ℝ × ℝ) = (0, 0) ∧
      (∀ (y : H2) (hy : y ∈ U),
        (y ∈ Set.range f ↔ ((h ⟨y, hy⟩ : V) : ℝ × ℝ).1 = 0) ∧
        (y ∈ Set.range g ↔ ((h ⟨y, hy⟩ : V) : ℝ × ℝ).2 = 0)) := by
  obtain ⟨B, hB⟩ := isometric_line_is_sl_axis f hf
  let e : H2 ≃ᵢ H2 := IsometryEquiv.constSMul B
  have heF (t : ℝ) : e.symm (f t) = verticalPath t := by
    rw [hB]
    exact e.symm_apply_apply _
  obtain ⟨D, hD⟩ := isometric_line_is_sl_axis (fun t => e.symm (g t))
    (e.symm.isometry.comp hg)
  let A := D⁻¹
  have hF (y : H2) : y ∈ Set.range f ↔ (e.symm y).re = 0 := by
    rw [← mem_vertical_range]
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, (heF t).symm⟩
    · rintro ⟨t, ht⟩
      exact ⟨t, e.symm.injective ((heF t).trans ht)⟩
  have hG (y : H2) : y ∈ Set.range g ↔ (A • e.symm y : H2).re = 0 := by
    rw [← mem_vertical_range]
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨t, ?_⟩
      rw [hD]
      simp [A]
    · rintro ⟨t, ht⟩
      refine ⟨t, e.symm.injective ?_⟩
      rw [hD]
      have hh := congrArg (fun w : H2 => D • w) ht
      simpa [A] using hh
  let α : ℝ := A 0 0 * A 1 0
  let β : ℝ := A 0 0 * A 1 1 + A 0 1 * A 1 0
  let δ : ℝ := A 0 1 * A 1 1
  have hGeq (y : H2) : y ∈ Set.range g ↔
      α * ((e.symm y).re^2+(e.symm y).im^2)+β*(e.symm y).re+δ = 0 := by
    exact (hG y).trans (sl_re_zero_iff A (e.symm y))
  have hzre : (e.symm z).re = 0 := (hF z).mp hz.1
  have hzeq := (hGeq z).mp hz.2
  have hα : α ≠ 0 := by
    intro hα
    have hδ : δ = 0 := by simpa [hα, hzre] using hzeq
    have hdet : A 0 0*A 1 1-A 0 1*A 1 0 = 1 := by
      simpa only [Matrix.det_fin_two] using A.property
    have hβsq : β^2 = 1 := by
      have hid : β^2 = (A 0 0*A 1 1-A 0 1*A 1 0)^2 + 4*α*δ := by
        dsimp [α, β, δ]
        ring
      rw [hid, hα, hdet]
      ring
    have hβ : β ≠ 0 := by intro h; rw [h] at hβsq; norm_num at hβsq
    apply hne
    ext y
    rw [hF, hGeq, hα, zero_mul, zero_add, hδ, add_zero, mul_eq_zero]
    simp [hβ]
  let c : ℝ := β/α
  let d : ℝ := δ/α
  let k : H2 ≃ₜ parabolaRegion c d := e.symm.toHomeomorph.trans (parabolaCoordinates c d)
  have hk (y : H2) : ((k y : parabolaRegion c d) : ℝ × ℝ) =
      ((e.symm y).re, (e.symm y).re^2+(e.symm y).im^2+c*(e.symm y).re+d) := rfl
  have hsecond (y : H2) : y ∈ Set.range g ↔ ((k y : parabolaRegion c d) : ℝ × ℝ).2 = 0 := by
    rw [hGeq, hk]
    dsimp [c, d]
    constructor <;> intro h <;> field_simp [hα] at * <;> nlinarith only [h]
  refine ⟨Set.univ, parabolaRegion c d, Set.mem_univ z,
    (Homeomorph.Set.univ H2).trans k, isOpen_univ, ?_, ?_, ?_⟩
  · exact isOpen_lt (by fun_prop) continuous_snd
  · apply Prod.ext
    · exact hzre
    · exact (hsecond z).mp hz.2
  · intro y hy
    exact ⟨hF y, hsecond y⟩

end CurveComplex.Hyperbolic.JointMinimum
