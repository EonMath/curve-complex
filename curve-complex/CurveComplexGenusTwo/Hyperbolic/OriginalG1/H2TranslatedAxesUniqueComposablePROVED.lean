import CurveComplexGenusTwo.Topology.ActualGeometryRelease.ActualHyperbolicAxisAllPROVED
import CurveComplexGenusTwo.Hyperbolic.CompactSegmentParametrization

namespace CurveComplex.Hyperbolic
open Matrix
open scoped MatrixGroups

private theorem diagonal_coordinates (r s : ℝ) (hr : r ≠ 0) (hs : s ≠ 0) (z : H2) :
    (axisDiagonalMatrix r s hr hs • z : H2).re = (r/s)*z.re ∧
    (axisDiagonalMatrix r s hr hs • z : H2).im = |r/s| *z.im := by
  constructor
  · rw [UpperHalfPlane.re_smul]
    simp [axisDiagonalMatrix, UpperHalfPlane.num, UpperHalfPlane.denom,
      Complex.div_re, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
    field_simp [hs]
  · rw [UpperHalfPlane.im_smul_eq_div_normSq]
    simp [GeneralLinearGroup.val_det_apply, axisDiagonalMatrix,
      GeneralLinearGroup.mkOfDetNeZero, Matrix.det_fin_two,
      UpperHalfPlane.denom, Complex.normSq_apply, abs_mul, abs_div]
    have hsa : |s| ≠ 0 := abs_ne_zero.mpr hs
    have hsq : s^2 = |s|^2 := (sq_abs s).symm
    rw [←pow_two s,hsq]
    field_simp [hsa]

private theorem scaling_segment_vertical (z w v : H2) (L : ℝ)
    (hL : 0 < L) (hL1 : L ≠ 1)
    (hwre : w.re = L*z.re) (hwim : w.im = L*z.im)
    (hvre : v.re = L^2*z.re) (hvim : v.im = L^2*z.im)
    (hseg : dist z w + dist w v = dist z v) : z.re = 0 := by
  have hc := metric_segment_circle_equation hseg
  simp only [Complex.normSq_apply] at hc
  change (v.re-z.re)*(w.re*w.re+w.im*w.im-(z.re*z.re+z.im*z.im)) =
    (w.re-z.re)*(v.re*v.re+v.im*v.im-(z.re*z.re+z.im*z.im)) at hc
  rw [hwre,hwim,hvre,hvim] at hc
  have hp : z.re * (z.re^2+z.im^2) * L * (L-1)^3 * (L+1) = 0 := by
    nlinarith only [hc]
  have hn : 0 < z.re^2+z.im^2 := by nlinarith [z.im_pos, sq_nonneg z.re]
  have hne : (z.re^2+z.im^2) * L * (L-1)^3 * (L+1) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hn.ne' hL.ne')
      (pow_ne_zero _ (sub_ne_zero.mpr hL1))) (by linarith)
  apply (mul_eq_zero.mp (by simpa only [mul_assoc] using hp)).resolve_right hne

private theorem real_isometry_surjective (f : ℝ → ℝ) (hf : Isometry f) :
    Function.Surjective f := by
  have h01 := hf.dist_eq 1 0
  simp only [Real.dist_eq, sub_zero, abs_one] at h01
  have hsign : f 1-f 0 = 1 ∨ f 1-f 0 = -1 := (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp h01
  have heq (t : ℝ) : (f t-f 0)^2=t^2 ∧ (f t-f 1)^2=(t-1)^2 := by
    have h0 := hf.dist_eq t 0
    have h1 := hf.dist_eq t 1
    simp only [Real.dist_eq, sub_zero] at h0 h1
    constructor
    · nlinarith only [sq_abs (f t-f 0),sq_abs t, congrArg (fun x : ℝ => x^2) h0]
    · nlinarith only [sq_abs (f t-f 1),sq_abs (t-1), congrArg (fun x : ℝ => x^2) h1]
  rcases hsign with hp | hn
  · have hall (t : ℝ) : f t = f 0+t := by
      obtain ⟨h0,h1⟩ := heq t
      nlinarith only [h0,h1,hp]
    intro y
    exact ⟨y-f 0,by rw [hall]; ring⟩
  · have hall (t : ℝ) : f t = f 0-t := by
      obtain ⟨h0,h1⟩ := heq t
      nlinarith only [h0,h1,hn]
    intro y
    exact ⟨f 0-y,by rw [hall]; ring⟩

private theorem vertical_line_range (f : ℝ → H2) (hf : Isometry f)
    (hx : ∀t, (f t).re = 0) : Set.range f=Set.range verticalPath := by
  let L : ℝ → ℝ := fun t => Real.log (f t).im
  have hL : Isometry L := Isometry.of_dist_eq fun t u => by
    change dist (Real.log (f t).im) (Real.log (f u).im) = dist t u
    rw [←UpperHalfPlane.dist_of_re_eq (by rw [hx t,hx u]), hf.dist_eq]
  have hv (t : ℝ) : f t = verticalPath (L t) := by
    apply UpperHalfPlane.ext_re_im
    · simpa [verticalPath] using hx t
    · simp [verticalPath,L,Real.exp_log (f t).im_pos]
  ext z
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨L t,(hv t).symm⟩
  · rintro ⟨t,rfl⟩
    obtain ⟨u,hu⟩ := real_isometry_surjective L hL t
    exact ⟨u,by rw [hv u,hu]⟩

private theorem diagonal_translated_line_vertical
    (r s : ℝ) (hr : r ≠ 0) (hs : s ≠ 0) (hk : |r/s| ≠ 1)
    (f : ℝ → H2) (hf : Isometry f) (p : ℝ)
    (ht : ∀t, (axisDiagonalMatrix r s hr hs • f t : H2) = f (t+p)) :
    ∀t, (f t).re = 0 := by
  let k := |r/s|
  have hkpos : 0 < k := abs_pos.mpr (div_ne_zero hr hs)
  have hksq : k^2 ≠ 1 := by
    intro h
    have : k = 1 := by nlinarith
    exact hk this
  have coords (t : ℝ) : (f (t+2*p)).re = k^2*(f t).re ∧
      (f (t+2*p)).im = k^2*(f t).im := by
    have h1 := diagonal_coordinates r s hr hs (f t)
    have h2 := diagonal_coordinates r s hr hs (f (t+p))
    rw [ht t] at h1
    rw [ht (t+p)] at h2
    have hadd : t+p+p=t+2*p := by ring
    rw [hadd] at h2
    constructor
    · rw [h2.1,h1.1]
      have hsq : (r/s)^2=k^2 := (sq_abs (r/s)).symm
      calc
        r/s*(r/s*(f t).re) = (r/s)^2*(f t).re := by ring
        _ = k^2*(f t).re := by rw [hsq]
    · rw [h2.2,h1.2]
      dsimp [k]
      ring
  intro t
  have h1 := coords t
  have h2 := coords (t+2*p)
  have hadd : t+2*p+2*p=t+4*p := by ring
  rw [hadd] at h2
  have hseg : dist (f t) (f (t+2*p))+dist (f (t+2*p)) (f (t+4*p)) =
      dist (f t) (f (t+4*p)) := by
    rw [hf.dist_eq,hf.dist_eq,hf.dist_eq]
    simp only [Real.dist_eq]
    have e1 : t-(t+2*p) =  -(2*p) := by ring
    have e2 : t+2*p-(t+4*p) =  -(2*p) := by ring
    have e3 : t-(t+4*p) =  -(4*p) := by ring
    rw [e1,e2,e3,abs_neg,abs_neg,abs_mul,abs_mul]
    norm_num
    ring
  apply scaling_segment_vertical (f t) (f (t+2*p)) (f (t+4*p)) (k^2)
    (sq_pos_of_pos hkpos) hksq h1.1 h1.2 _ _ hseg
  · rw [h2.1,h1.1]; ring
  · rw [h2.2,h1.2]; ring

theorem actual_h2_translated_isometric_lines_same_range
    (g : H2 ≃ᵢ H2) (a b : ℝ → H2) (ha : Isometry a) (hb : Isometry b)
    (ε : ℝ) (hε : 0 < ε) (hdisplacement : ∀ z : H2, ε ≤ dist z (g z))
    (p q : ℝ) (hp : p ≠ 0) (hq : q ≠ 0)
    (htranslate_a : ∀ t : ℝ, g (a t) = a (t+p))
    (htranslate_b : ∀ t : ℝ, g (b t) = b (t+q)) :
    Set.range a = Set.range b := by
  obtain ⟨A,hA⟩ := axis_metric_isometry_gl_representation g
  have hdispA (z : H2) : ε ≤ dist z (A • z) := by rw [←hA z]; exact hdisplacement z
  have hdiscr := axis_uniform_gl_discriminant_pos A ε hε hdispA
  obtain ⟨T,r,s,hr,hs,hmat⟩ := axis_discriminant_positive_diagonalization A hdiscr
  let D := axisDiagonalMatrix r s hr hs
  let Tgl := SpecialLinearGroup.mapGL ℝ T
  have hgl : A*Tgl=Tgl*D := by
    apply Units.ext
    change A.val*T.val=T.val*!![r,0;0,s]
    exact hmat
  let e : H2 ≃ᵢ H2 := IsometryEquiv.constSMul T
  have hconj (z : H2) : g (e z) = e (D • z) := by
    rw [hA]
    change A • (Tgl • z) = Tgl • (D • z)
    rw [←mul_smul,hgl,mul_smul]
  have hk : |r/s| ≠ 1 := by
    intro hk
    have hfix : g (e (verticalPath 0)) = e (verticalPath 0) := by
      rw [hconj]
      dsimp [D]
      rw [axis_diagonal_vertical_translation,hk,Real.log_one,add_zero]
    have h := hdisplacement (e (verticalPath 0))
    rw [hfix,dist_self] at h
    exact (not_le_of_gt hε) h
  let f : ℝ → H2 := fun t => e.symm (a t)
  let k : ℝ → H2 := fun t => e.symm (b t)
  have hf : Isometry f := e.symm.isometry.comp ha
  have hki : Isometry k := e.symm.isometry.comp hb
  have htf (t : ℝ) : (D • f t : H2) = f (t+p) := by
    apply e.injective
    rw [←hconj]
    simpa [f] using htranslate_a t
  have htk (t : ℝ) : (D • k t : H2) = k (t+q) := by
    apply e.injective
    rw [←hconj]
    simpa [k] using htranslate_b t
  have hrf := vertical_line_range f hf
    (diagonal_translated_line_vertical r s hr hs hk f hf p htf)
  have hrk := vertical_line_range k hki
    (diagonal_translated_line_vertical r s hr hs hk k hki q htk)
  have hfk : Set.range f=Set.range k := hrf.trans hrk.symm
  ext z
  constructor
  · rintro ⟨t,rfl⟩
    have hm : f t ∈ Set.range k := hfk ▸ Set.mem_range_self t
    obtain ⟨u,hu⟩ := hm
    refine ⟨u,?_⟩
    have := congrArg e hu
    simpa [f,k] using this
  · rintro ⟨t,rfl⟩
    have hm : k t ∈ Set.range f := hfk.symm ▸ Set.mem_range_self t
    obtain ⟨u,hu⟩ := hm
    refine ⟨u,?_⟩
    have := congrArg e hu
    simpa [f,k] using this

end CurveComplex.Hyperbolic
