import CurveComplexGenusTwo.Topology.ActualGeometryRelease.ActualHyperbolicAxisAllPROVED
import CurveComplexGenusTwo.Hyperbolic.Cayley
import Mathlib.Analysis.Complex.Basic
open Complex
private theorem disk_norm_gap (u v w : ℂ) :
    normSq (star v*w+star u) - normSq (u*w+v) =
      (normSq u-normSq v)*(1-normSq w) := by
  simp only [Complex.star_def,Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.mul_re,
    Complex.mul_im,Complex.conj_re,Complex.conj_im]
  ring
private theorem disk_denominator_nonzero (u v w : ℂ) (hgap : normSq v < normSq u) (hw : normSq w ≤ 1) :
    star v*w+star u ≠ 0 := by
  intro h
  have he : star v*w = -(star u) := eq_neg_of_add_eq_zero_left h
  have hn := congrArg normSq he
  simp only [Complex.star_def,Complex.normSq_mul,Complex.normSq_conj,Complex.normSq_neg] at hn
  have hv := Complex.normSq_nonneg v
  nlinarith

private theorem disk_mobius_norm_le_one (u v w : ℂ) (hgap : normSq v < normSq u) (hw : normSq w ≤ 1) :
    normSq ((u*w+v)/(star v*w+star u)) ≤ 1 := by
  have hden := disk_denominator_nonzero u v w hgap hw
  have hd : 0 < normSq (star v*w+star u) := Complex.normSq_pos.mpr hden
  rw [Complex.normSq_div]
  apply (div_le_iff₀ hd).mpr
  have h := disk_norm_gap u v w
  have hmul : 0 ≤ (normSq u-normSq v)*(1-normSq w) :=
    mul_nonneg (sub_nonneg.mpr hgap.le) (sub_nonneg.mpr hw)
  nlinarith

private theorem disk_mobius_boundary (u v w : ℂ) (hgap : normSq v < normSq u) (hw : normSq w ≤ 1) :
    normSq ((u*w+v)/(star v*w+star u)) = 1 ↔ normSq w = 1 := by
  have hden := disk_denominator_nonzero u v w hgap hw
  have hd : 0 < normSq (star v*w+star u) := Complex.normSq_pos.mpr hden
  have hg := disk_norm_gap u v w
  rw [Complex.normSq_div,div_eq_one_iff_eq hd.ne']
  constructor
  · intro heq
    have hz : (normSq u-normSq v)*(1-normSq w) = 0 := by linarith
    have hfactor := (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (ne_of_gt hgap))
    linarith
  · intro hw1
    rw [hw1] at hg
    linarith

private theorem disk_mobius_inverse (u v w : ℂ) (hgap : normSq v < normSq u) (hw : normSq w ≤ 1) :
    (star u*((u*w+v)/(star v*w+star u))-v)/
      (-(star v)*((u*w+v)/(star v*w+star u))+u) = w := by
  have hden := disk_denominator_nonzero u v w hgap hw
  have hmem := disk_mobius_norm_le_one u v w hgap hw
  have hgap' : normSq (-v) < normSq (star u) := by
    simpa only [Complex.star_def,Complex.normSq_conj,Complex.normSq_neg] using hgap
  have hden' := disk_denominator_nonzero (star u) (-v)
    ((u*w+v)/(star v*w+star u)) hgap' hmem
  simp only [star_neg,star_star] at hden'
  apply (div_eq_iff hden').mpr
  have hc : (star v*w+star u)*(star v*w+star u)⁻¹ = 1 := mul_inv_cancel₀ hden
  simp only [div_eq_mul_inv]
  linear_combination (v+w*u)*hc

private theorem disk_mobius_homeomorphism (u v : ℂ) (hgap : normSq v < normSq u) :
    ∃ e : Metric.closedBall (0:ℂ) 1 ≃ₜ Metric.closedBall (0:ℂ) 1,
      ∀ w : Metric.closedBall (0:ℂ) 1,
        (e w : ℂ) = (u*(w:ℂ)+v)/(star v*(w:ℂ)+star u) := by
  let D := Metric.closedBall (0:ℂ) 1
  have hmem (w : D) : normSq (w:ℂ) ≤ 1 := by
    have hnorm : ‖(w:ℂ)‖ ≤ 1 := by
      have hh := w.property
      change dist (w:ℂ) 0 ≤ 1 at hh
      simpa only [dist_zero_right] using hh
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (w:ℂ)]
  have hgap' : normSq (-v) < normSq (star u) := by
    simpa only [Complex.star_def,Complex.normSq_conj,Complex.normSq_neg] using hgap
  have make (a b : ℂ) (hg : normSq b < normSq a) :
      ∃ F : C(D,D), ∀ w : D, (F w:ℂ) = (a*(w:ℂ)+b)/(star b*(w:ℂ)+star a) := by
    let F : D → D := fun w => ⟨(a*(w:ℂ)+b)/(star b*(w:ℂ)+star a),by
      change dist _ 0 ≤ 1
      rw [dist_zero_right]
      have hh := disk_mobius_norm_le_one a b (w:ℂ) hg (hmem w)
      rw [Complex.normSq_eq_norm_sq] at hh
      nlinarith [norm_nonneg ((a*(w:ℂ)+b)/(star b*(w:ℂ)+star a))]⟩
    have hcont : Continuous F := by
      apply Continuous.subtype_mk
      exact ((continuous_const.mul continuous_subtype_val).add continuous_const).div
        ((continuous_const.mul continuous_subtype_val).add continuous_const)
        (fun w => disk_denominator_nonzero a b (w:ℂ) hg (hmem w))
    exact ⟨⟨F,hcont⟩,fun _ => rfl⟩
  obtain ⟨F,hF⟩ := make u v hgap
  obtain ⟨G,hG⟩ := make (star u) (-v) hgap'
  have hGF (w : D) : G (F w) = w := by
    apply Subtype.ext
    rw [hG,hF]
    simp only [star_neg,star_star,← sub_eq_add_neg]
    exact disk_mobius_inverse u v (w:ℂ) hgap (hmem w)
  have hFG (w : D) : F (G w) = w := by
    apply Subtype.ext
    rw [hF,hG]
    have h := disk_mobius_inverse (star u) (-v) (w:ℂ) hgap' (hmem w)
    simpa only [star_neg,star_star,neg_neg,sub_neg_eq_add,← sub_eq_add_neg] using h
  let e : D ≃ D :=
    { toFun := F
      invFun := G
      left_inv := hGF
      right_inv := hFG }
  let h : D ≃ₜ D :=
    { toEquiv := e
      continuous_toFun := F.continuous
      continuous_invFun := G.continuous }
  exact ⟨h,hF⟩
private theorem sl_coefficient_gap (a b c d : ℝ) (hdet : a*d-b*c=1) :
    normSq ((a-d:ℝ)-Complex.I*(b+c:ℝ)) <
      normSq ((a+d:ℝ)+Complex.I*(b-c:ℝ)) := by
  have hg : normSq ((a+d:ℝ)+Complex.I*(b-c:ℝ)) -
      normSq ((a-d:ℝ)-Complex.I*(b+c:ℝ)) = 4*(a*d-b*c) := by
    simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.sub_re,
      Complex.sub_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im]
    ring
  rw [hdet] at hg
  linarith

private theorem sl_numerator_identity (a b c d : ℝ) (z : ℂ) :
    (((a+d:ℝ)+Complex.I*(b-c:ℝ))*(z-Complex.I)+
      ((a-d:ℝ)-Complex.I*(b+c:ℝ))*(z+Complex.I)) =
      2*(((a:ℂ)*z+b)-Complex.I*((c:ℂ)*z+d)) := by
  apply Complex.ext <;>
    simp only [Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im] <;> norm_num <;> ring
private theorem sl_denominator_identity (a b c d : ℝ) (z : ℂ) :
    (star ((a-d:ℝ)-Complex.I*(b+c:ℝ))*(z-Complex.I)+
      star ((a+d:ℝ)+Complex.I*(b-c:ℝ))*(z+Complex.I)) =
      2*(((a:ℂ)*z+b)+Complex.I*((c:ℂ)*z+d)) := by
  apply Complex.ext <;>
    simp only [Complex.star_def,Complex.conj_re,Complex.conj_im,
      Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im] <;> norm_num <;> ring

private theorem sl_cayley_intertwining (a b c d : ℝ) (z : ℂ)
    (hD : (c:ℂ)*z+d ≠ 0) (hz : z+Complex.I ≠ 0) :
    ((((a:ℂ)*z+b)/((c:ℂ)*z+d))-Complex.I)/
      ((((a:ℂ)*z+b)/((c:ℂ)*z+d))+Complex.I) =
    ((((a+d:ℝ)+Complex.I*(b-c:ℝ))*((z-Complex.I)/(z+Complex.I))+
      ((a-d:ℝ)-Complex.I*(b+c:ℝ))))/
    ((star ((a-d:ℝ)-Complex.I*(b+c:ℝ)))*((z-Complex.I)/(z+Complex.I))+
      star ((a+d:ℝ)+Complex.I*(b-c:ℝ))) := by
  rw [div_sub' hD,div_add' _ _ _ hD,div_div_div_cancel_right₀ hD]
  rw [mul_div,div_add' _ _ _ hz,mul_div,div_add' _ _ _ hz,
    div_div_div_cancel_right₀ hz]
  rw [sl_numerator_identity,sl_denominator_identity]
  rw [mul_div_mul_left _ _ (by norm_num : (2:ℂ) ≠ 0)]
  congr 1 <;> ring

open scoped UpperHalfPlane MatrixGroups
open CurveComplex.Hyperbolic
private theorem actual_sl_disk_extension (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    ∃ e : Metric.closedBall (0:ℂ) 1 ≃ₜ Metric.closedBall (0:ℂ) 1,
      (∀ z : H2, e (cayley z) = cayley (A • z)) ∧
      (∀ w : Metric.closedBall (0:ℂ) 1, ‖(e w:ℂ)‖ = 1 ↔ ‖(w:ℂ)‖ = 1) := by
  let u : ℂ := ((A 0 0+A 1 1:ℝ):ℂ)+Complex.I*((A 0 1-A 1 0:ℝ):ℂ)
  let v : ℂ := ((A 0 0-A 1 1:ℝ):ℂ)-Complex.I*((A 0 1+A 1 0:ℝ):ℂ)
  have hdet : A 0 0*A 1 1-A 0 1*A 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using A.property
  have hgap : normSq v < normSq u := sl_coefficient_gap _ _ _ _ hdet
  obtain ⟨e,he⟩ := disk_mobius_homeomorphism u v hgap
  refine ⟨e,?_,?_⟩
  · intro z
    apply Subtype.ext
    rw [he]
    have hD : (A 1 0:ℂ)*(z:ℂ)+(A 1 1:ℂ) ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_im,Complex.ofReal_re,
        Complex.zero_im,zero_mul,zero_add,add_zero] at him
      have hc := (mul_eq_zero.mp him).resolve_right z.im_ne_zero
      have hre := congrArg Complex.re h
      simp only [hc,Complex.ofReal_zero,zero_mul,zero_add,Complex.ofReal_re,Complex.zero_re] at hre
      rw [hc,hre] at hdet
      norm_num at hdet
    have hz : (z:ℂ)+Complex.I ≠ 0 := by
      intro h
      have hh := congrArg Complex.im h
      simp only [Complex.add_im,Complex.I_im,Complex.zero_im] at hh
      change z.im+1 = 0 at hh
      linarith [z.im_pos]
    have hi := sl_cayley_intertwining (A 0 0) (A 0 1) (A 1 0) (A 1 1) (z:ℂ) hD hz
    change (u*((cayley z:ℂ))+v)/(star v*((cayley z:ℂ))+star u) = _
    change (u*((((z:ℂ)-Complex.I)/((z:ℂ)+Complex.I)))+v)/
      (star v*((((z:ℂ)-Complex.I)/((z:ℂ)+Complex.I)))+star u) =
      (((A • z: H2):ℂ)-Complex.I)/(((A • z: H2):ℂ)+Complex.I)
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simpa only [Algebra.algebraMap_self, RingHom.id_apply,u,v] using hi.symm
  · intro w
    have hnorm : ‖(w:ℂ)‖ ≤ 1 := by
      have hh := w.property
      change dist (w:ℂ) 0 ≤ 1 at hh
      simpa only [dist_zero_right] using hh
    have hw : normSq (w:ℂ) ≤ 1 := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg (w:ℂ)]
    have hiff := disk_mobius_boundary u v (w:ℂ) hgap hw
    rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq] at hiff
    rw [he]
    constructor
    · intro hn
      have hW := hiff.mp (by rw [hn]; norm_num)
      nlinarith [norm_nonneg (w:ℂ)]
    · intro hn
      have hF := hiff.mpr (by rw [hn]; norm_num)
      nlinarith [norm_nonneg ((u*(w:ℂ)+v)/(star v*(w:ℂ)+star u))]

private theorem actual_reflection_disk_extension : ∃ e : Metric.closedBall (0:ℂ) 1 ≃ₜ Metric.closedBall (0:ℂ) 1,
    (∀ z : H2, e (cayley z) = cayley (axisZeroReflection z)) ∧
    (∀ w : Metric.closedBall (0:ℂ) 1, ‖(e w:ℂ)‖ = ‖(w:ℂ)‖) := by
  let D := Metric.closedBall (0:ℂ) 1
  let F : D → D := fun w => ⟨star (w:ℂ),by
    have hw := w.property
    change dist (w:ℂ) 0 ≤ 1 at hw
    change dist (star (w:ℂ)) 0 ≤ 1
    simpa only [dist_zero_right,norm_star] using hw⟩
  have hF : Continuous F :=
    (continuous_star.comp continuous_subtype_val).subtype_mk _
  have hFF : Function.Involutive F := by intro w; apply Subtype.ext; exact star_star _
  let e : D ≃ₜ D :=
    { toEquiv := hFF.toPerm F
      continuous_toFun := hF
      continuous_invFun := hF }
  refine ⟨e,?_,?_⟩
  · intro z
    apply Subtype.ext
    change star (((z:ℂ)-Complex.I)/((z:ℂ)+Complex.I)) =
      ((-star (z:ℂ))-Complex.I)/((-star (z:ℂ))+Complex.I)
    rw [star_div₀,star_sub,star_add]
    have hi : star Complex.I = -Complex.I := by simp [Complex.star_def]
    rw [hi]
    have hn : -star (z:ℂ)-Complex.I = -(star (z:ℂ)+Complex.I) := by ring
    have hd : -star (z:ℂ)+Complex.I = -(star (z:ℂ)-Complex.I) := by ring
    rw [hn,hd,neg_div_neg_eq]
    congr 1 <;> ring
  · intro w
    change ‖star (w:ℂ)‖ = ‖(w:ℂ)‖
    exact norm_star _


namespace CurveComplex.Hyperbolic
/-- Source Fact3.5 simplicity: actual hyperbolic isometries extend to the
closed Cayley disk, so deck-translated proper lifted curves acquire their
actual transported ideal endpoints. This includes orientation-reversing
isometries and supplies no desired crossing/embedding certificate. -/
theorem actual_h2_isometry_closed_disk_extension (g : H2 ≃ᵢ H2) :
    ∃ e : Metric.closedBall (0:ℂ) 1 ≃ₜ Metric.closedBall (0:ℂ) 1,
      (∀ z : H2, e (cayley z) = cayley (g z)) ∧
      (∀ z : Metric.closedBall (0:ℂ) 1, ‖(e z : ℂ)‖ = 1 ↔ ‖(z:ℂ)‖ = 1) := by
  obtain ⟨A,hA | hA⟩ := axis_metric_isometry_mobius_or_antimobius g
  · obtain ⟨e,he,hboundary⟩ := actual_sl_disk_extension A
    refine ⟨e,?_,hboundary⟩
    intro z
    rw [hA,he]
  · obtain ⟨e,he,hboundary⟩ := actual_sl_disk_extension A
    obtain ⟨r,hr,hnorm⟩ := actual_reflection_disk_extension
    refine ⟨r.trans e,?_,?_⟩
    · intro z
      rw [Homeomorph.trans_apply,hr,he,hA]
    · intro z
      change ‖(e (r z):ℂ)‖ = 1 ↔ ‖(z:ℂ)‖ = 1
      rw [hboundary,hnorm]

end CurveComplex.Hyperbolic
