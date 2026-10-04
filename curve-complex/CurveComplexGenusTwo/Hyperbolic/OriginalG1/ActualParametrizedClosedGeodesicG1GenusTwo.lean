import CurveComplexGenusTwo.Topology.TorusPrimitiveLift
import CurveComplexGenusTwo.Topology.OriginalCircleCollar.CircleCollarOriginalPackage
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Order.ArchimedeanDiscrete
import Mathlib.GroupTheory.GroupAction.SubMulAction.OfStabilizer
import Mathlib.Algebra.Group.Action.TransferInstance
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.ActualDeckDevelopmentIsometryPROVED
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.G1ArbitraryCrosscutAlternationPROVED
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.H2IsometryClosedDiskExtensionPROVED
import CurveComplexGenusTwo.Topology.LocalSurgery.ActualReturningSubarc
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.OriginalLoopDefinitions
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.ActualComponentHyperbolicDevelopmentPROVED
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.ActualHyperbolicAxisAllPROVED
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.H2LocalUnitGeodesicPROVED
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.H2TranslatedAxesUniqueComposablePROVED
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

namespace CurveComplex.Hyperbolic

open Matrix
open scoped UpperHalfPlane MatrixGroups

private noncomputable def actualLogarithmicAxisCoordinates : H2 ≃ₜ ℝ × ℝ where
  toFun z := (Real.log z.im,z.re/z.im)
  invFun w := ⟨⟨Real.exp w.1*w.2,Real.exp w.1⟩,Real.exp_pos _⟩
  left_inv z := by
    apply UpperHalfPlane.ext_re_im
    · change Real.exp (Real.log z.im)*(z.re/z.im)=z.re
      rw [Real.exp_log z.im_pos]
      field_simp
    · exact Real.exp_log z.im_pos
  right_inv w := by
    apply Prod.ext
    · exact Real.log_exp w.1
    · change Real.exp w.1*w.2/Real.exp w.1=w.2
      field_simp
  continuous_toFun := by
    apply Continuous.prodMk
    · exact UpperHalfPlane.continuous_im.log (fun z => ne_of_gt z.im_pos)
    · exact UpperHalfPlane.continuous_re.div UpperHalfPlane.continuous_im
        (fun z => ne_of_gt z.im_pos)
  continuous_invFun := by
    apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
    change Continuous (fun w : ℝ × ℝ => (⟨Real.exp w.1*w.2,Real.exp w.1⟩:ℂ))
    have hc : Continuous (fun w : ℝ × ℝ =>
        ((Real.exp w.1*w.2 : ℝ):ℂ)+((Real.exp w.1:ℝ):ℂ)*Complex.I) :=
      (Complex.continuous_ofReal.comp ((Real.continuous_exp.comp continuous_fst).mul
        continuous_snd)).add ((Complex.continuous_ofReal.comp
          (Real.continuous_exp.comp continuous_fst)).mul continuous_const)
    convert hc using 1
    funext w
    apply Complex.ext <;> simp only [Complex.add_re,
      Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,Complex.mul_re,Complex.mul_im,
      Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_mul,sub_zero,add_zero,zero_add]

private theorem actual_logarithmic_axis_dilation (g : H2 ≃ᵢ H2) (L : ℝ)
    (hd : ∀z : H2, (g z).re=Real.exp L*z.re ∧ (g z).im=Real.exp L*z.im)
    (z : H2) : actualLogarithmicAxisCoordinates (g z)=
      actualLogarithmicAxisCoordinates z+(L,0) := by
  apply Prod.ext
  · change Real.log (g z).im=Real.log z.im+L
    rw [(hd z).2,Real.log_mul (Real.exp_ne_zero _) (ne_of_gt z.im_pos),Real.log_exp]
    ring
  · change (g z).re/(g z).im=z.re/z.im+0
    rw [(hd z).1,(hd z).2,add_zero]
    field_simp

private theorem actual_translation_power_coordinates {G X : Type} [Group G] [MulAction G X]
    (η : G) (e : X → ℝ × ℝ) (a b : ℝ)
    (he : ∀x, e (η • x)=e x+(a,b)) :
    ∀k : ℤ, ∀x, e (η^k • x)=e x+((k:ℝ)*a,(k:ℝ)*b) := by
  intro k
  induction k using Int.induction_on with
  | zero => intro x; simp
  | succ n hn =>
    intro x
    rw [_root_.zpow_add,zpow_one,mul_smul,hn,he]
    ext <;> simp only [Prod.fst_add,Prod.snd_add,Int.cast_add,Int.cast_one] <;> ring
  | pred n hn =>
    intro x
    have hi (y : X) : e (η⁻¹ • y)=e y-(a,b) := by
      have hh := he (η⁻¹ • y)
      simp only [smul_inv_smul] at hh
      rw [hh]
      abel
    rw [_root_.zpow_sub,zpow_one,mul_smul,hn,hi]
    ext <;> simp only [Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub,
      Int.cast_sub,Int.cast_one] <;> ring

private theorem actual_translated_axis_dilation_or_glide (g : H2 ≃ᵢ H2) (L : ℝ)
    (hperiod : ∀t : ℝ, g (verticalPath t)=verticalPath (t+L)) :
    (∀z : H2, (g z).re=Real.exp L*z.re ∧ (g z).im=Real.exp L*z.im) ∨
    (∀z : H2, (g z).re= -Real.exp L*z.re ∧ (g z).im=Real.exp L*z.im) := by
  let r : ℝ := Real.exp (L/2)
  have hr : r ≠ 0 := Real.exp_ne_zero _
  let A : SL(2,ℝ) := ⟨!![r,0;0,r⁻¹],by simp [Matrix.det_fin_two,hr]⟩
  let D : H2 ≃ᵢ H2 := IsometryEquiv.constSMul A
  have hr2 : r^2=Real.exp L := by
    change (Real.exp (L/2))^2=Real.exp L
    rw [pow_two,←Real.exp_add]
    congr 1
    ring
  have hDcoe (z : H2) : (D z:ℂ)=(Real.exp L:ℂ)*(z:ℂ) := by
    change (A • z:H2).coe=_
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    change ((r:ℂ)*(z:ℂ)+0)/(0*(z:ℂ)+((r⁻¹:ℝ):ℂ))=(Real.exp L:ℂ)*(z:ℂ)
    simp only [add_zero,zero_mul,zero_add,Complex.ofReal_inv,div_inv_eq_mul]
    have hh : (r:ℂ)*(z:ℂ)*(r:ℂ)=((r^2:ℝ):ℂ)*(z:ℂ) := by push_cast; ring
    rw [hh,hr2]
  have hDre (z : H2) : (D z).re=Real.exp L*z.re := by
    change (D z:ℂ).re=Real.exp L*(z:ℂ).re
    have h := congrArg Complex.re (hDcoe z)
    simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using h
  have hDim (z : H2) : (D z).im=Real.exp L*z.im := by
    change (D z:ℂ).im=Real.exp L*(z:ℂ).im
    have h := congrArg Complex.im (hDcoe z)
    simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero] using h
  have hDvertical (t : ℝ) : D (verticalPath t)=verticalPath (t+L) := by
    apply UpperHalfPlane.ext_re_im
    · rw [hDre]
      simp [verticalPath]
    · rw [hDim]
      change Real.exp L*Real.exp t=Real.exp (t+L)
      rw [←Real.exp_add,add_comm]
  let h : H2 ≃ᵢ H2 := g.trans D.symm
  have hvert (t : ℝ) : h (verticalPath t)=verticalPath t := by
    change D.symm (g (verticalPath t))=verticalPath t
    rw [hperiod,←hDvertical,D.symm_apply_apply]
  have hI : h UpperHalfPlane.I=UpperHalfPlane.I := by
    have hv0 : verticalPath 0=UpperHalfPlane.I := by
      apply UpperHalfPlane.ext_re_im <;> simp [verticalPath]
    simpa only [hv0] using hvert 0
  rcases axis_normalized_isometry_identity_or_reflection h hI (hvert 1) with hid | hreflect
  · left
    intro z
    have hz : g z=D z := by
      have ht := congrArg D (hid z)
      simpa only [h,IsometryEquiv.trans_apply,D.apply_symm_apply] using ht
    rw [hz]
    exact ⟨hDre z,hDim z⟩
  · right
    intro z
    have hz : g z=D (axisZeroReflection z) := by
      have ht := congrArg D (hreflect z)
      simpa only [h,IsometryEquiv.trans_apply,D.apply_symm_apply] using ht
    rw [hz,hDre,hDim,axisZeroReflection_re,axisZeroReflection_im]
    constructor
    · ring
    · rfl


open Filter Topology Set Matrix TopologicalSpace Bundle Path.Homotopic.Quotient CurveComplex.LocalSurgery
open Schoenflies
open scoped Manifold ContDiff UpperHalfPlane ENNReal unitInterval MatrixGroups Pointwise
set_option maxHeartbeats 4000000

section
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
private theorem actual_sl_disk_extension_with_formula (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    let u : ℂ := ((A 0 0+A 1 1:ℝ):ℂ)+Complex.I*((A 0 1-A 1 0:ℝ):ℂ)
    let v : ℂ := ((A 0 0-A 1 1:ℝ):ℂ)-Complex.I*((A 0 1+A 1 0:ℝ):ℂ)
    ∃ e : Metric.closedBall (0:ℂ) 1 ≃ₜ Metric.closedBall (0:ℂ) 1,
      (∀ w, (e w:ℂ)=(u*(w:ℂ)+v)/(star v*(w:ℂ)+star u)) ∧
      (∀ z : H2, e (cayley z) = cayley (A • z)) ∧
      (∀ w : Metric.closedBall (0:ℂ) 1, ‖(e w:ℂ)‖ = 1 ↔ ‖(w:ℂ)‖ = 1) := by
  dsimp only
  let u : ℂ := ((A 0 0+A 1 1:ℝ):ℂ)+Complex.I*((A 0 1-A 1 0:ℝ):ℂ)
  let v : ℂ := ((A 0 0-A 1 1:ℝ):ℂ)-Complex.I*((A 0 1+A 1 0:ℝ):ℂ)
  have hdet : A 0 0*A 1 1-A 0 1*A 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using A.property
  have hgap : normSq v < normSq u := sl_coefficient_gap _ _ _ _ hdet
  obtain ⟨e,he⟩ := disk_mobius_homeomorphism u v hgap
  refine ⟨e,he,?_,?_⟩
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


private theorem actual_disk_plus_endpoint (a b c d : ℝ) :
    let u : ℂ := ((a+d:ℝ):ℂ)+Complex.I*((b-c:ℝ):ℂ)
    let v : ℂ := ((a-d:ℝ):ℂ)-Complex.I*((b+c:ℝ):ℂ)
    (u*1+v)/(star v*1+star u) = ((a:ℂ)-Complex.I*(c:ℂ))/((a:ℂ)+Complex.I*(c:ℂ)) := by
  dsimp
  have hn : (((a+d:ℝ):ℂ)+Complex.I*((b-c:ℝ):ℂ))*1+
      (((a-d:ℝ):ℂ)-Complex.I*((b+c:ℝ):ℂ)) = 2*((a:ℂ)-Complex.I*(c:ℂ)) := by push_cast; ring
  have hd : star (((a-d:ℝ):ℂ)-Complex.I*((b+c:ℝ):ℂ))*1+
      star (((a+d:ℝ):ℂ)+Complex.I*((b-c:ℝ):ℂ)) = 2*((a:ℂ)+Complex.I*(c:ℂ)) := by
    simp only [star_add,star_sub,star_mul,Complex.star_def,Complex.conj_ofReal,Complex.conj_I]
    push_cast
    ring
  change _ / (star _ * _ + star _) = _
  rw [hn,hd]
  exact mul_div_mul_left _ _ (by norm_num : (2:ℂ) ≠ 0)
private theorem actual_disk_minus_endpoint (a b c d : ℝ) :
    let u : ℂ := ((a+d:ℝ):ℂ)+Complex.I*((b-c:ℝ):ℂ)
    let v : ℂ := ((a-d:ℝ):ℂ)-Complex.I*((b+c:ℝ):ℂ)
    (u*(-1)+v)/(star v*(-1)+star u) = ((b:ℂ)-Complex.I*(d:ℂ))/((b:ℂ)+Complex.I*(d:ℂ)) := by
  dsimp
  have hn : (((a+d:ℝ):ℂ)+Complex.I*((b-c:ℝ):ℂ))*(-1)+
      (((a-d:ℝ):ℂ)-Complex.I*((b+c:ℝ):ℂ)) = (-2*Complex.I)*((b:ℂ)-Complex.I*(d:ℂ)) := by
    push_cast
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im] <;> ring
  have hd : star (((a-d:ℝ):ℂ)-Complex.I*((b+c:ℝ):ℂ))*(-1)+
      star (((a+d:ℝ):ℂ)+Complex.I*((b-c:ℝ):ℂ)) = (-2*Complex.I)*((b:ℂ)+Complex.I*(d:ℂ)) := by
    simp only [star_add,star_sub,star_mul,Complex.star_def,Complex.conj_ofReal,Complex.conj_I]
    push_cast
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im] <;> ring
  change _ / (star _ * _ + star _) = _
  rw [hn,hd]
  exact mul_div_mul_left _ _ (mul_ne_zero (by norm_num) Complex.I_ne_zero)

private theorem actual_sl_disk_endpoints (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (left right : Metric.closedBall (0:ℂ) 1)
    (hleft : (left:ℂ)=-1) (hright : (right:ℂ)=1) :
    ∃ e : Metric.closedBall (0:ℂ) 1 ≃ₜ Metric.closedBall (0:ℂ) 1,
      (∀ z : H2, e (cayley z)=cayley (A • z)) ∧
      (∀ w : Metric.closedBall (0:ℂ) 1, ‖(e w:ℂ)‖=1 ↔ ‖(w:ℂ)‖=1) ∧
      (e left:ℂ)=((A 0 1:ℂ)-Complex.I*(A 1 1:ℂ))/((A 0 1:ℂ)+Complex.I*(A 1 1:ℂ)) ∧
      (e right:ℂ)=((A 0 0:ℂ)-Complex.I*(A 1 0:ℂ))/((A 0 0:ℂ)+Complex.I*(A 1 0:ℂ)) := by
  obtain ⟨e,he,hinterior,hboundary⟩ := actual_sl_disk_extension_with_formula A
  refine ⟨e,hinterior,hboundary,?_,?_⟩
  · rw [he,hleft]
    exact actual_disk_minus_endpoint _ _ _ _
  · rw [he,hright]
    exact actual_disk_plus_endpoint _ _ _ _

private theorem actual_vertical_crossing_equation (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (t : ℝ)
    (hcross : (A • verticalPath t : H2).re = 0) :
    A 0 0*A 1 0*(Real.exp t)^2+A 0 1*A 1 1=0 := by
  have hdet : A 0 0*A 1 1-A 0 1*A 1 0=1 := by
    simpa only [Matrix.det_fin_two] using A.property
  have hden : 0 < (A 1 0)^2*(Real.exp t)^2+(A 1 1)^2 := by
    by_cases hc : A 1 0=0
    · have hd : A 1 1 ≠ 0 := by
        intro hd
        rw [hc,hd] at hdet
        norm_num at hdet
      simp only [hc,zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_mul,zero_add]
      exact sq_pos_of_ne_zero hd
    · have hp := mul_pos (sq_pos_of_ne_zero hc) (sq_pos_of_pos (Real.exp_pos t))
      nlinarith [sq_nonneg (A 1 1)]
  have hre : (A • verticalPath t : H2).re =
      (A 0 0*A 1 0*(Real.exp t)^2+A 0 1*A 1 1)/
        ((A 1 0)^2*(Real.exp t)^2+(A 1 1)^2) := by
    change ((A • verticalPath t : H2):ℂ).re = _
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp [verticalPath,Complex.div_re,Complex.mul_re,Complex.mul_im,
      Complex.normSq_apply]
    congr 1 <;> ring
  rw [hre] at hcross
  exact (div_eq_zero_iff.mp hcross).resolve_right hden.ne'

private theorem actual_crossing_product (a b c d y : ℝ) (hy : 0 < y)
    (hcross : a*c*y^2+b*d=0) (hne : a*c ≠ 0) :
    (a*c)*(b*d) < 0 := by
  have hs : 0 < y^2 := sq_pos_of_pos hy
  have ha : 0 < (a*c)^2 := sq_pos_of_ne_zero hne
  have he : (a*c)*(b*d) = -(a*c)^2*y^2 := by
    linear_combination (a*c)*hcross
  rw [he]
  have := mul_pos ha hs
  nlinarith
private theorem actual_degenerate_crossing (a b c d : ℝ) (hdet : a*d-b*c=1)
    (hz : a*c=0) (hw : b*d=0) :
    (b=0 ∧ c=0) ∨ (a=0 ∧ d=0) := by
  rcases mul_eq_zero.mp hz with ha | hc
  · right
    rcases mul_eq_zero.mp hw with hb | hd
    · rw [ha,hb] at hdet; norm_num at hdet
    · exact ⟨ha,hd⟩
  · left
    rcases mul_eq_zero.mp hw with hb | hd
    · exact ⟨hb,hc⟩
    · rw [hc,hd] at hdet; norm_num at hdet
private theorem ideal_endpoint_im (a c : ℝ) :
    (((a:ℂ)-Complex.I*(c:ℂ))/((a:ℂ)+Complex.I*(c:ℂ))).im =
      (-2*a*c)/(a^2+c^2) := by
  simp only [Complex.div_im,Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,
    Complex.I_im,Complex.normSq_apply]
  congr 1 <;> ring
private theorem actual_endpoint_product (a b c d : ℝ) (hcross : (a*c)*(b*d) < 0) :
    (((a:ℂ)-Complex.I*(c:ℂ))/((a:ℂ)+Complex.I*(c:ℂ))).im *
    (((b:ℂ)-Complex.I*(d:ℂ))/((b:ℂ)+Complex.I*(d:ℂ))).im < 0 := by
  rw [ideal_endpoint_im,ideal_endpoint_im,div_mul_div_comm]
  have hnon : (a*c)*(b*d) ≠ 0 := ne_of_lt hcross
  have ha : a ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hnon).1).1
  have hb : b ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hnon).2).1
  have hdenA : 0 < a^2+c^2 := by nlinarith [sq_pos_of_ne_zero ha,sq_nonneg c]
  have hdenB : 0 < b^2+d^2 := by nlinarith [sq_pos_of_ne_zero hb,sq_nonneg d]
  apply div_neg_of_neg_of_pos _ (mul_pos hdenA hdenB)
  nlinarith [hcross]

private theorem actual_sl_crossing_disk_sign (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (t : ℝ)
    (hcross : (A • verticalPath t : H2).re=0) (hne : A 0 0*A 1 0 ≠ 0)
    (left right : Metric.closedBall (0:ℂ) 1)
    (hleft : (left:ℂ)=-1) (hright : (right:ℂ)=1) :
    ∃ e : Metric.closedBall (0:ℂ) 1 ≃ₜ Metric.closedBall (0:ℂ) 1,
      (∀ z : H2, e (cayley z)=cayley (A • z)) ∧
      (∀ w : Metric.closedBall (0:ℂ) 1, ‖(e w:ℂ)‖=1 ↔ ‖(w:ℂ)‖=1) ∧
      (e left:ℂ).im*(e right:ℂ).im < 0 := by
  obtain ⟨e,he,hboundary,hl,hr⟩ := actual_sl_disk_endpoints A left right hleft hright
  refine ⟨e,he,hboundary,?_⟩
  rw [hl,hr,mul_comm]
  apply actual_endpoint_product
  exact actual_crossing_product _ _ _ _ _ (Real.exp_pos t)
    (actual_vertical_crossing_equation A t hcross) hne

private theorem actual_reflection_disk_extension : ∃ e : Metric.closedBall (0:ℂ) 1 ≃ₜ Metric.closedBall (0:ℂ) 1,
    (∀ z : H2, e (cayley z) = cayley (axisZeroReflection z)) ∧
    (∀ w : Metric.closedBall (0:ℂ) 1, ‖(e w:ℂ)‖ = ‖(w:ℂ)‖) ∧
    (∀ w : Metric.closedBall (0:ℂ) 1, (e w:ℂ)=star (w:ℂ)) := by
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
  refine ⟨e,?_,?_,?_⟩
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
  · intro w
    rfl

private theorem actual_isometry_crossing_disk_sign (g : H2 ≃ᵢ H2) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (t : ℝ)
    (hA : (∀ z : H2, g z=A • z) ∨ (∀ z : H2, g z=A • axisZeroReflection z))
    (hcross : (A • verticalPath t : H2).re=0) (hne : A 0 0*A 1 0 ≠ 0)
    (left right : Metric.closedBall (0:ℂ) 1)
    (hleft : (left:ℂ)=-1) (hright : (right:ℂ)=1) :
    ∃ e : Metric.closedBall (0:ℂ) 1 ≃ₜ Metric.closedBall (0:ℂ) 1,
      (∀ z : H2, e (cayley z)=cayley (g z)) ∧
      (∀ w : Metric.closedBall (0:ℂ) 1, ‖(e w:ℂ)‖=1 ↔ ‖(w:ℂ)‖=1) ∧
      (e left:ℂ).im*(e right:ℂ).im < 0 := by
  obtain ⟨e,he,hboundary,hsign⟩ := actual_sl_crossing_disk_sign A t hcross hne left right hleft hright
  rcases hA with hA | hA
  · refine ⟨e,?_,hboundary,hsign⟩
    intro z
    rw [hA]
    exact he z
  · obtain ⟨r,hr,hrnorm,hrformula⟩ := actual_reflection_disk_extension
    have hl : r left=left := by
      apply Subtype.ext
      rw [hrformula,hleft]
      simp
    have hright' : r right=right := by
      apply Subtype.ext
      rw [hrformula,hright]
      simp
    refine ⟨r.trans e,?_,?_,?_⟩
    · intro z
      change e (r (cayley z))=cayley (g z)
      rw [hr,he,hA]
    · intro w
      change ‖(e (r w):ℂ)‖=1 ↔ ‖(w:ℂ)‖=1
      rw [hboundary,hrnorm]
    · simpa only [Homeomorph.trans_apply,hl,hright'] using hsign

private theorem actual_sl_crossing_equation (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (t : ℝ)
    (hcross : (A • verticalPath t : H2).re = 0) :
    A 0 0*A 1 0*(Real.exp t)^2+A 0 1*A 1 1=0 := by
  have hdet : A 0 0*A 1 1-A 0 1*A 1 0=1 := by
    simpa only [Matrix.det_fin_two] using A.property
  have hden : 0 < (A 1 0)^2*(Real.exp t)^2+(A 1 1)^2 := by
    by_cases hc : A 1 0=0
    · have hd : A 1 1 ≠ 0 := by
        intro hd
        rw [hc,hd] at hdet
        norm_num at hdet
      simp only [hc,zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_mul,zero_add]
      exact sq_pos_of_ne_zero hd
    · have hp := mul_pos (sq_pos_of_ne_zero hc) (sq_pos_of_pos (Real.exp_pos t))
      nlinarith [sq_nonneg (A 1 1)]
  have hre : (A • verticalPath t : H2).re =
      (A 0 0*A 1 0*(Real.exp t)^2+A 0 1*A 1 1)/
        ((A 1 0)^2*(Real.exp t)^2+(A 1 1)^2) := by
    change ((A • verticalPath t : H2):ℂ).re = _
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp [verticalPath,Complex.div_re,Complex.mul_re,Complex.mul_im,
      Complex.normSq_apply]
    congr 1 <;> ring
  rw [hre] at hcross
  exact (div_eq_zero_iff.mp hcross).resolve_right hden.ne'

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


private theorem actual_sl_vertical_re (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (t : ℝ) :
    (A • verticalPath t : H2).re =
      (A 0 0*A 1 0*(Real.exp t)^2+A 0 1*A 1 1)/
        ((A 1 0)^2*(Real.exp t)^2+(A 1 1)^2) := by
  change ((A • verticalPath t : H2):ℂ).re = _
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [verticalPath,Complex.div_re,Complex.mul_re,Complex.mul_im,Complex.normSq_apply]
  congr 1 <;> ring
private theorem actual_distinct_axis_crossing_nonzero (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (t : ℝ)
    (hcross : (A • verticalPath t : H2).re = 0)
    (hne : Set.range (fun s : ℝ => A • verticalPath s) ≠ Set.range verticalPath) :
    A 0 0*A 1 0 ≠ 0 := by
  intro hac
  have h := actual_sl_crossing_equation A t hcross
  rw [hac] at h
  have hbd : A 0 1*A 1 1=0 := by simpa using h
  have hx (s : ℝ) : (A • verticalPath s : H2).re=0 := by
    rw [actual_sl_vertical_re,hac,hbd]
    simp
  have hi : Isometry (fun s : ℝ => A • verticalPath s) :=
    (IsometryEquiv.constSMul A).isometry.comp verticalPath_isometry
  exact hne (vertical_line_range (fun s : ℝ => A • verticalPath s) hi hx)

private theorem actual_distinct_isometry_axis_crossing_disk_sign (g : H2 ≃ᵢ H2) (t : ℝ)
    (hcross : (g (verticalPath t)).re=0)
    (hne : Set.range (fun s : ℝ => g (verticalPath s)) ≠ Set.range verticalPath)
    (left right : Metric.closedBall (0:ℂ) 1)
    (hleft : (left:ℂ)=-1) (hright : (right:ℂ)=1) :
    ∃ e : Metric.closedBall (0:ℂ) 1 ≃ₜ Metric.closedBall (0:ℂ) 1,
      (∀ z : H2, e (cayley z)=cayley (g z)) ∧
      (∀ w : Metric.closedBall (0:ℂ) 1, ‖(e w:ℂ)‖=1 ↔ ‖(w:ℂ)‖=1) ∧
      (e left:ℂ).im*(e right:ℂ).im < 0 := by
  obtain ⟨A,hA⟩ := axis_metric_isometry_mobius_or_antimobius g
  have hv : ∀ s : ℝ, g (verticalPath s)=A • verticalPath s := by
    intro s
    rcases hA with hA | hA
    · exact hA _
    · rw [hA]
      congr 1
      apply UpperHalfPlane.ext_re_im <;> simp [axisZeroReflection,verticalPath]
  have hc : (A • verticalPath t : H2).re=0 := by rw [←hv]; exact hcross
  have hd : Set.range (fun s : ℝ => A • verticalPath s) ≠ Set.range verticalPath := by
    simpa only [←hv] using hne
  exact actual_isometry_crossing_disk_sign g A t hA hc
    (actual_distinct_axis_crossing_nonzero A t hc hd) left right hleft hright

end
private theorem actual_embedded_lift_stabilizer_shift {P E : Type} [TopologicalSpace P] [TopologicalSpace E]
    (q : P → E) (hq : IsCoveringMap q) (f : C(Circle,E)) (hf : IsEmbedding f)
    (coordinate : AddCircle (1:ℝ) ≃ₜ Circle) (Γ : C(ℝ,P))
    (hprojection : ∀ t : ℝ, q (Γ t) = f (coordinate (t : AddCircle (1:ℝ))))
    (η : P ≃ₜ P) (hη : ∀ z, q (η z) = q z)
    (hstable : η (Γ 0) ∈ Set.range Γ) :
    ∃ k : ℤ, ∀ t : ℝ, η (Γ t) = Γ (t+k) := by
  obtain ⟨x,hx⟩ := hstable
  have hc : (x : AddCircle (1:ℝ)) = 0 := by
    apply coordinate.injective
    apply hf.injective
    change f (coordinate (x:AddCircle (1:ℝ))) = f (coordinate ((0:ℝ):AddCircle (1:ℝ)))
    rw [← hprojection x,← hprojection 0,hx,hη]
  obtain ⟨k,hk⟩ := (AddCircle.coe_eq_zero_iff (p := (1:ℝ))).mp hc
  have hkx : (k:ℝ) = x := by simpa using hk
  rw [← hkx] at hx
  refine ⟨k,?_⟩
  have heq : (fun t : ℝ => η (Γ t)) = (fun t : ℝ => Γ (t+k)) := by
    refine hq.eq_of_comp_eq (η.continuous.comp Γ.continuous)
      (Γ.continuous.comp (continuous_id.add continuous_const)) ?_ 0 ?_
    · funext t
      change q (η (Γ t)) = q (Γ (t+k))
      rw [hη,hprojection,hprojection,AddCircle.coe_add]
      have hz : ((k:ℝ):AddCircle (1:ℝ)) = 0 :=
        (AddCircle.coe_eq_zero_iff (p := (1:ℝ))).mpr ⟨k,by simp⟩
      rw [hz,add_zero]
    · simpa only [zero_add] using hx.symm
  exact congrFun heq

private theorem actual_integer_deck_equivariance {G X : Type} [Group G] [MulAction G X]
    (δ : G) (Γ : ℝ → X) (hΓ : ∀ t : ℝ, Γ (t+1)=δ • Γ t) :
    ∀ n : ℤ, ∀ t : ℝ, Γ (t+n)=δ^n • Γ t := by
  intro n
  induction n using Int.induction_on with
  | zero => intro t; simp
  | succ n hn =>
    intro t
    rw [Int.cast_add,Int.cast_one,←add_assoc,hΓ,hn,_root_.zpow_add]
    simp only [zpow_one,mul_smul]
    rw [←mul_smul,←mul_smul]
    congr 1
    exact (Commute.self_zpow δ n).eq
  | pred n hn =>
    intro t
    have hp : Γ (t-1)=δ⁻¹ • Γ t := by
      have h := hΓ (t-1)
      rw [sub_add_cancel] at h
      rw [h]
      simp
    rw [Int.cast_sub,Int.cast_one]
    rw [show t+(((-n:ℤ):ℝ)-1)=(t-1)+((-n:ℤ):ℝ) by ring,hn,hp]
    simp only [_root_.zpow_sub,zpow_one,mul_smul]

private theorem actual_embedded_lift_stabilizer_monodromy {P E : Type} [TopologicalSpace P] [TopologicalSpace E]
    (q : P → E) (hq : IsQuotientCoveringMap q (deck q))
    (f : C(Circle,E)) (hf : IsEmbedding f)
    (coordinate : AddCircle (1:ℝ) ≃ₜ Circle) (Γ : C(ℝ,P))
    (hprojection : ∀ t : ℝ, q (Γ t)=f (coordinate (t:AddCircle (1:ℝ))))
    (δ η : deck q) (hΓ : ∀ t : ℝ, Γ (t+1)=δ • Γ t)
    (hstable : η • Γ 0 ∈ Set.range Γ) :
    ∃ k : ℤ, η=δ^k := by
  obtain ⟨k,hk⟩ := actual_embedded_lift_stabilizer_shift q hq.isCoveringMap f hf
    coordinate Γ hprojection η.val (fun z => hq.map_smul η) hstable
  refine ⟨k,?_⟩
  have hi := actual_integer_deck_equivariance δ Γ hΓ k 0
  have := hq.isCancelSMul
  apply IsCancelSMul.right_cancel _ _ (Γ 0)
  have h := hk 0
  change η • Γ 0=Γ (0+(k:ℝ)) at h
  exact h.trans hi

private theorem actual_scaled_integer_deck_equivariance {G X : Type} [Group G] [MulAction G X]
    (δ : G) (a : ℝ → X) (p : ℝ) (hp : p ≠ 0)
    (ha : ∀ t : ℝ, a (t+p)=δ • a t) (k : ℤ) (t : ℝ) :
    a (t+(k:ℝ)*p)=δ^k • a t := by
  let b : ℝ → X := fun s => a (s*p)
  have hb : ∀ s : ℝ, b (s+1)=δ • b s := by
    intro s
    change a ((s+1)*p)=δ • a (s*p)
    rw [add_mul,one_mul,ha]
  have h := actual_integer_deck_equivariance δ b hb k (t/p)
  change a ((t/p+(k:ℝ))*p)=δ^k • a ((t/p)*p) at h
  rw [add_mul,div_mul_cancel₀ t hp] at h
  exact h
private theorem actual_deck_power_axis_range {G X : Type} [Group G] [MulAction G X]
    (δ : G) (a : ℝ → X) (p : ℝ) (hp : p ≠ 0)
    (ha : ∀ t : ℝ, a (t+p)=δ • a t) (k : ℤ) :
    Set.range (fun t : ℝ => δ^k • a t)=Set.range a := by
  ext x
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨t+(k:ℝ)*p,actual_scaled_integer_deck_equivariance δ a p hp ha k t⟩
  · rintro ⟨t,rfl⟩
    refine ⟨t-(k:ℝ)*p,?_⟩
    change δ^k • a (t-(k:ℝ)*p)=a t
    rw [←actual_scaled_integer_deck_equivariance δ a p hp ha k]
    congr 1
    ring
private theorem actual_real_isometry_translation_or_reflection (f : ℝ → ℝ) (hf : Isometry f) :
    (∀t, f t=f 0+t) ∨ (∀t, f t=f 0-t) := by
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
    exact Or.inl hall
  · have hall (t : ℝ) : f t = f 0-t := by
      obtain ⟨h0,h1⟩ := heq t
      nlinarith only [h0,h1,hn]
    exact Or.inr hall


private theorem actual_free_real_action_translation_hom {G : Type} [Group G] [MulAction G ℝ] [IsCancelSMul G ℝ]
    (hmetric : ∀ g : G, Isometry (fun t : ℝ => g • t)) :
    ∃ ρ : Additive G →+ ℝ,
      Function.Injective ρ ∧ ∀ g : G, ∀ t : ℝ, g • t=t+ρ (Additive.ofMul g) := by
  have htranslate (g : G) (t : ℝ) : g • t=t+g • (0:ℝ) := by
    rcases actual_real_isometry_translation_or_reflection (fun t : ℝ => g • t)
      (hmetric g) with hplus | hminus
    · rw [hplus,add_comm]
    · have hfix : g • ((g • (0:ℝ))/2)=(g • (0:ℝ))/2 := by rw [hminus]; ring
      have hg : g=1 := IsCancelSMul.right_cancel _ _ ((g • (0:ℝ))/2) (by simpa only [one_smul] using hfix)
      subst g
      have hh := hminus 1
      norm_num at hh
  let ρ : Additive G →+ ℝ :=
    { toFun := fun g => g.toMul • (0:ℝ)
      map_zero' := by simp
      map_add' := by
        intro g h
        change (g.toMul*h.toMul) • (0:ℝ)=g.toMul • (0:ℝ)+h.toMul • (0:ℝ)
        rw [mul_smul,htranslate,add_comm] }
  refine ⟨ρ,?_,?_⟩
  · intro g h heq
    have hg : g.toMul=h.toMul := IsCancelSMul.right_cancel _ _ (0:ℝ) heq
    exact congrArg Additive.ofMul hg
  · intro g t
    exact htranslate g t

private theorem actual_source_axis_stabilizer_translation_hom {E P : Type} [MetricSpace E] [TopologicalSpace P]
    (p : P → E) (hq : IsQuotientCoveringMap p (deck p))
    (e : P ≃ₜ H2)
    (hmetric : ∀x : P, ∃U : Set P, IsOpen U ∧ x∈U ∧
      ∀y∈U, ∀z∈U, dist (p y) (p z)=dist (e y) (e z)) :
    let a : ℝ → P := fun t => e.symm (verticalPath t)
    let K := MulAction.stabilizer (deck p) (Set.range a)
    ∃ ρ : Additive K →+ ℝ, Function.Injective ρ ∧
      ∀η : K, ∀t : ℝ, e (η.val • a t)=verticalPath (t+ρ (Additive.ofMul η)) := by
  classical
  let a : ℝ → P := fun t => e.symm (verticalPath t)
  let K := MulAction.stabilizer (deck p) (Set.range a)
  have hainj : Function.Injective a := e.symm.injective.comp verticalPath_isometry.injective
  let coord : ℝ ≃ Set.range a := Equiv.ofInjective a hainj
  letI : MulAction K ℝ := coord.mulAction K
  have hcoord (η : K) (t : ℝ) : a (η • t)=η.val • a t := by
    have h := congrArg Subtype.val (coord.apply_symm_apply (η • coord t))
    exact h
  letI : IsCancelSMul (deck p) P := hq.isCancelSMul
  letI : IsCancelSMul K ℝ :=
    { right_cancel' := by
        intro η θ t heq
        apply Subtype.ext
        apply IsCancelSMul.right_cancel _ _ (a t)
        rw [←hcoord,←hcoord,heq] }
  have hrealmetric (η : K) : Isometry (fun t : ℝ => η • t) := by
    have hη := actual_deck_development_isometry p e hmetric η.val.val
      (fun x => hq.map_smul η.val)
    have hecoord (t : ℝ) :
        ((e.symm.trans η.val.val).trans e) (verticalPath t)=verticalPath (η • t) := by
      rw [←e.apply_symm_apply (verticalPath (η • t))]
      change e (η.val • a t)=e (a (η • t))
      rw [hcoord]
    apply Isometry.of_dist_eq
    intro t u
    have h := hη.dist_eq (verticalPath t) (verticalPath u)
    rw [hecoord,hecoord,verticalPath_isometry.dist_eq,verticalPath_isometry.dist_eq] at h
    exact h
  obtain ⟨ρ,hρ,htranslate⟩ := actual_free_real_action_translation_hom hrealmetric
  refine ⟨ρ,hρ,?_⟩
  intro η t
  rw [←hcoord,htranslate]
  exact e.apply_symm_apply _

private theorem actual_cover_axis_period_isolation {P E G : Type} [TopologicalSpace P] [TopologicalSpace E]
    [Group G] [MulAction G P]
    (q : P → E) (hq : IsQuotientCoveringMap q G)
    (e : P ≃ₜ UpperHalfPlane) (a : ℝ → UpperHalfPlane) (ha : Isometry a) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ η : G, ∀ r : ℝ,
      e (η • e.symm (a 0))=a r → |r| < ε → η=1 := by
  obtain ⟨U,hU,hdisjoint⟩ := hq.disjoint (e.symm (a 0))
  have hpre : e.symm ⁻¹' U ∈ 𝓝 (a 0) :=
    e.symm.continuous.continuousAt.preimage_mem_nhds hU
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨ε,hε,?_⟩
  intro η r hr hsmall
  have hηU : η • e.symm (a 0) ∈ U := by
    have hdist : dist (e (η • e.symm (a 0))) (a 0) < ε := by
      rw [hr,ha.dist_eq,Real.dist_eq,sub_zero]
      exact hsmall
    have hm := hball hdist
    simpa only [Set.mem_preimage,e.symm_apply_apply] using hm
  apply hdisjoint η
  refine ⟨η • e.symm (a 0),?_,hηU⟩
  exact ⟨e.symm (a 0),mem_of_mem_nhds hU,rfl⟩

private theorem actual_gap_discrete (K : AddSubgroup ℝ) (ε : ℝ) (hε : 0 < ε)
    (hgap : ∀ r ∈ K, |r| < ε → r=0) : DiscreteTopology K := by
  apply discreteTopology_of_isOpen_singleton_zero
  rw [isOpen_induced_iff]
  refine ⟨Metric.ball (0:ℝ) ε,Metric.isOpen_ball,?_⟩
  ext r
  constructor
  · intro hr
    apply Set.mem_singleton_iff.mpr
    apply Subtype.ext
    have hd : |(r:ℝ)| < ε := by simpa only [Set.mem_preimage,Metric.mem_ball,Real.dist_eq,sub_zero] using hr
    exact hgap r r.property hd
  · intro hr
    have hz : r=0 := Set.mem_singleton_iff.mp hr
    subst r
    simpa only [Set.mem_preimage,AddSubgroup.coe_zero,Metric.mem_ball,dist_self] using hε
private theorem actual_discrete_cyclic (K : AddSubgroup ℝ) [DiscreteTopology K] : ∃ r : ℝ, K=AddSubgroup.zmultiples r := by
  have hcyclic : IsAddCyclic K := AddSubgroup.discrete_iff_addCyclic.mpr inferInstance
  obtain ⟨r,hr⟩ := (K.isAddCyclic_iff_exists_zmultiples_eq_top).mp hcyclic
  exact ⟨r,hr.symm⟩

private theorem actual_positive_minimal_period (K : AddSubgroup ℝ) (ε p : ℝ) (hε : 0 < ε) (hp : 0 < p)
    (hpK : p ∈ K) (hgap : ∀ r ∈ K, |r| < ε → r=0) :
    ∃ ℓ : ℝ, 0 < ℓ ∧ K=AddSubgroup.zmultiples ℓ := by
  letI : DiscreteTopology K := actual_gap_discrete K ε hε hgap
  obtain ⟨r,hr⟩ := actual_discrete_cyclic K
  have hrne : r ≠ 0 := by
    intro hz
    rw [hr,hz] at hpK
    have hpzero : p=0 := by simpa using hpK
    exact hp.ne' hpzero
  refine ⟨|r|,abs_pos.mpr hrne,?_⟩
  rcases le_or_gt 0 r with hnonneg | hnegative
  · simpa only [abs_of_nonneg hnonneg] using hr
  · simpa only [abs_of_neg hnegative,AddSubgroup.zmultiples_neg] using hr

private theorem actual_source_axis_minimal_period {E P : Type} [MetricSpace E] [TopologicalSpace P]
    (p : P → E) (hq : IsQuotientCoveringMap p (deck p))
    (e : P ≃ₜ H2)
    (hmetric : ∀x : P, ∃U : Set P, IsOpen U ∧ x∈U ∧
      ∀y∈U, ∀z∈U, dist (p y) (p z)=dist (e y) (e z))
    (δ : deck p) (period : ℝ) (hperiod : 0 < period)
    (hδ : ∀t : ℝ, e (δ • e.symm (verticalPath t))=verticalPath (t+period)) :
    let a : ℝ → P := fun t => e.symm (verticalPath t)
    let K := MulAction.stabilizer (deck p) (Set.range a)
    ∃ ρ : Additive K →+ ℝ, Function.Injective ρ ∧
      (∀η : K, ∀t : ℝ, e (η.val • a t)=verticalPath (t+ρ (Additive.ofMul η))) ∧
      ∃ ℓ : ℝ, 0 < ℓ ∧ ∃ η : K, ρ (Additive.ofMul η)=ℓ ∧
        ρ.range=AddSubgroup.zmultiples ℓ := by
  classical
  let a : ℝ → P := fun t => e.symm (verticalPath t)
  let K := MulAction.stabilizer (deck p) (Set.range a)
  obtain ⟨ρ,hρ,htranslate⟩ := actual_source_axis_stabilizer_translation_hom p hq e hmetric
  refine ⟨ρ,hρ,htranslate,?_⟩
  obtain ⟨ε,hε,hisolated⟩ := actual_cover_axis_period_isolation p hq e verticalPath verticalPath_isometry
  have hgap : ∀r∈ρ.range, |r| < ε → r=0 := by
    intro r hr hsmall
    obtain ⟨η,hη⟩ := hr
    have hge := htranslate η.toMul 0
    change e (η.toMul.val • e.symm (verticalPath 0))=verticalPath (0+ρ η) at hge
    rw [zero_add,hη] at hge
    have heq := hisolated η.toMul.val r hge hsmall
    have hkzero : η.toMul=(1:K) := Subtype.ext heq
    have hηzero : η=0 := congrArg Additive.ofMul hkzero
    subst η
    simpa using hη.symm
  have ha (t : ℝ) : a (t+period)=δ • a t := by
    apply e.injective
    change e (e.symm (verticalPath (t+period)))=e (δ • e.symm (verticalPath t))
    rw [e.apply_symm_apply]
    exact (hδ t).symm
  have hδK : δ∈K := by
    apply MulAction.mem_stabilizer_iff.mpr
    change (fun z : P => δ • z) '' Set.range a=Set.range a
    apply Set.Subset.antisymm
    · rintro _ ⟨_,⟨t,rfl⟩,rfl⟩
      exact ⟨t+period,ha t⟩
    · rintro _ ⟨t,rfl⟩
      refine ⟨a (t-period),Set.mem_range_self _,?_⟩
      change δ • a (t-period)=a t
      rw [←ha,sub_add_cancel]
  let δK : K := ⟨δ,hδK⟩
  have hvalue : ρ (Additive.ofMul δK)=period := by
    have hv := htranslate δK 0
    rw [zero_add] at hv
    apply verticalPath_isometry.injective
    exact hv.symm.trans (by simpa only [zero_add] using hδ 0)
  have hpimage : period∈ρ.range := ⟨Additive.ofMul δK,hvalue⟩
  obtain ⟨ℓ,hℓ,hperiods⟩ := actual_positive_minimal_period ρ.range ε period hε hperiod hpimage hgap
  have hℓimage : ℓ∈ρ.range := by
    rw [hperiods]
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨1,by simp⟩
  obtain ⟨η,hη⟩ := hℓimage
  exact ⟨ℓ,hℓ,η.toMul,hη,hperiods⟩
theorem actual_canonical_deck_axis_minimal_period {E P : Type} [MetricSpace E] [TopologicalSpace P]
    (p : P → E) (hq : IsQuotientCoveringMap p (deck p))
    (e : P ≃ₜ H2)
    (hmetric : ∀x : P, ∃U : Set P, IsOpen U ∧ x∈U ∧
      ∀y∈U, ∀z∈U, dist (p y) (p z)=dist (e y) (e z))
    (δ : deck p) (period : ℝ) (hperiod : 0 < period)
    (hδ : ∀t : ℝ, e (δ • e.symm (verticalPath t))=verticalPath (t+period)) :
    let a : ℝ → P := fun t => e.symm (verticalPath t)
    let K := MulAction.stabilizer (deck p) (Set.range a)
    ∃ ρ : Additive K →+ ℝ, Function.Injective ρ ∧
      (∀η : K, ∀t : ℝ, e (η.val • a t)=verticalPath (t+ρ (Additive.ofMul η))) ∧
      ∃ ℓ : ℝ, 0 < ℓ ∧ ∃ η : K, ρ (Additive.ofMul η)=ℓ ∧
        ρ.range=AddSubgroup.zmultiples ℓ :=
  actual_source_axis_minimal_period p hq e hmetric δ period hperiod hδ

private theorem actual_minimal_period_circle_embedding {E : Type} [TopologicalSpace E] [T2Space E]
    (path : C(ℝ,E)) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (hperiod : Function.Periodic path ℓ)
    (hfibre : ∀t u : ℝ, path t=path u → ∃n : ℤ, t-u=(n:ℝ)*ℓ) :
    ∃ g : C(Circle,E), IsEmbedding g ∧
      ∀t : ℝ, g (AddCircle.homeomorphCircle hℓ.ne' (t:AddCircle ℓ))=path t := by
  let descended : C(AddCircle ℓ,E) :=
    ⟨hperiod.lift,continuous_coinduced_dom.mpr path.continuous⟩
  have hdesc : Function.Injective descended := by
    intro z w h
    obtain ⟨t,rfl⟩ := QuotientAddGroup.mk_surjective z
    obtain ⟨u,rfl⟩ := QuotientAddGroup.mk_surjective w
    change path t=path u at h
    obtain ⟨n,hn⟩ := hfibre t u h
    apply sub_eq_zero.mp
    rw [←AddCircle.coe_sub]
    apply (AddCircle.coe_eq_zero_iff (p:=ℓ)).mpr
    exact ⟨n,by simpa only [zsmul_eq_mul] using hn.symm⟩
  let coordinate : AddCircle ℓ ≃ₜ Circle := AddCircle.homeomorphCircle hℓ.ne'
  let g : C(Circle,E) := descended.comp ⟨coordinate.symm,coordinate.symm.continuous⟩
  refine ⟨g,?_,?_⟩
  · exact (g.continuous.isClosedEmbedding (hdesc.comp coordinate.symm.injective)).isEmbedding
  · intro t
    change descended (coordinate.symm (coordinate (t:AddCircle ℓ)))=path t
    rw [coordinate.symm_apply_apply]
    rfl

private theorem actual_source_minimal_axis_curve {E P : Type} [MetricSpace E] [TopologicalSpace P]
    (p : P → E) (hq : IsQuotientCoveringMap p (deck p))
    (e : P ≃ₜ H2)
    (hmetric : ∀x : P, ∃U : Set P, IsOpen U ∧ x∈U ∧
      ∀y∈U, ∀z∈U, dist (p y) (p z)=dist (e y) (e z))
    (δ : deck p) (period : ℝ) (hperiod : 0 < period)
    (hδ : ∀t : ℝ, e (δ • e.symm (verticalPath t))=verticalPath (t+period))
    (haxis : ∀ η : deck p, ∀t u : ℝ,
      η • e.symm (verticalPath u)=e.symm (verticalPath t) →
      η∈MulAction.stabilizer (deck p) (Set.range (fun s : ℝ => e.symm (verticalPath s)))) :
    ∃ ℓ : ℝ, ∃ hℓ : 0 < ℓ, ∃ g : C(Circle,E), IsEmbedding g ∧
      (∀t : ℝ, g (AddCircle.homeomorphCircle hℓ.ne' (t:AddCircle ℓ))=
        p (e.symm (verticalPath t))) ∧
      ∃ η₀ : deck p, (∀t : ℝ, η₀ • e.symm (verticalPath t)=e.symm (verticalPath (t+ℓ))) ∧
        ∀ ζ : deck p, ∀ r : ℝ, e (ζ • e.symm (verticalPath 0))=verticalPath r →
          ∃n : ℤ, r=(n:ℝ)*ℓ := by
  classical
  let a : ℝ → P := fun t => e.symm (verticalPath t)
  let K := MulAction.stabilizer (deck p) (Set.range a)
  obtain ⟨ρ,hρ,htranslate,ℓ,hℓ,η,hη,hperiods⟩ :=
    actual_source_axis_minimal_period p hq e hmetric δ period hperiod hδ
  let path : C(ℝ,E) :=
    ⟨fun t => p (a t),hq.isCoveringMap.continuous.comp
      (e.symm.continuous.comp verticalPath_isometry.continuous)⟩
  have hpathperiod : Function.Periodic path ℓ := by
    intro t
    have ht := htranslate η t
    rw [hη] at ht
    have hlift : η.val • a t=a (t+ℓ) := by
      apply e.injective
      exact ht.trans (e.apply_symm_apply _).symm
    change p (a (t+ℓ))=p (a t)
    rw [←hlift]
    exact hq.map_smul η.val
  have hfibre : ∀t u : ℝ, path t=path u → ∃n : ℤ, t-u=(n:ℝ)*ℓ := by
    intro t u htu
    obtain ⟨ζ,hζ⟩ := hq.apply_eq_iff_mem_orbit.mp htu
    have hζK : ζ∈K := haxis ζ t u hζ
    let ζK : K := ⟨ζ,hζK⟩
    have ht := htranslate ζK u
    change e (ζ • a u)=verticalPath (u+ρ (Additive.ofMul ζK)) at ht
    change ζ • a u=a t at hζ
    rw [hζ] at ht
    have he : t=u+ρ (Additive.ofMul ζK) := by
      apply verticalPath_isometry.injective
      exact (e.apply_symm_apply _).symm.trans ht
    have hm : ρ (Additive.ofMul ζK)∈AddSubgroup.zmultiples ℓ := by
      rw [←hperiods]
      exact ⟨Additive.ofMul ζK,rfl⟩
    obtain ⟨n,hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hm
    refine ⟨n,?_⟩
    rw [zsmul_eq_mul] at hn
    linarith
  obtain ⟨g,hg,hclock⟩ := actual_minimal_period_circle_embedding path ℓ hℓ hpathperiod hfibre
  refine ⟨ℓ,hℓ,g,hg,hclock,η.val,?_,?_⟩
  · intro t
    apply e.injective
    have ht := htranslate η t
    rw [hη] at ht
    exact ht.trans (e.apply_symm_apply _).symm
  · intro ζ r hr
    have hmeet : ζ • e.symm (verticalPath 0)=e.symm (verticalPath r) := by
      apply e.injective
      exact hr.trans (e.apply_symm_apply _).symm
    let ζK : K := ⟨ζ,haxis ζ r 0 hmeet⟩
    have ht := htranslate ζK 0
    rw [zero_add] at ht
    have hvalue : ρ (Additive.ofMul ζK)=r := by
      apply verticalPath_isometry.injective
      exact ht.symm.trans hr
    have hm : ρ (Additive.ofMul ζK)∈AddSubgroup.zmultiples ℓ := by
      rw [←hperiods]
      exact ⟨Additive.ofMul ζK,rfl⟩
    obtain ⟨n,hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hm
    exact ⟨n,by simpa only [zsmul_eq_mul,hvalue] using hn.symm⟩

private theorem actual_lifted_axis_collar_excludes_glide {E P : Type} [TopologicalSpace E] [TopologicalSpace P]
    (p : P → E) (hp : IsCoveringMap p) (dev : P ≃ₜ H2)
    (L : ℝ) (hL : 0 < L) (η : P ≃ₜ P) (hη : ∀x, p (η x)=p x)
    (collar : C(Set.Ioo (-1:ℝ) 1 × Circle,E)) (hinj : Function.Injective collar)
    (hcore : ∀t : ℝ, collar (⟨0,by norm_num⟩,
      AddCircle.homeomorphCircle hL.ne' (t:AddCircle L))=p (dev.symm (verticalPath t)))
    (hperiod : ∀t : ℝ, η (dev.symm (verticalPath t))=dev.symm (verticalPath (t+L)))
    (scale : ℝ) (hscale : 0 < scale)
    (hflip : ∀z : H2, (dev (η (dev.symm z))).re= -scale*z.re) : False := by
  let W := Set.Ioo (-1:ℝ) 1
  let zeroWidth : W := ⟨0,by norm_num [W]⟩
  let positiveWidth : W := ⟨1/2,by norm_num [W]⟩
  letI : ContractibleSpace W := (convex_Ioo (-1:ℝ) 1 : Convex ℝ W).contractibleSpace ⟨0,by norm_num [W]⟩
  letI : LocallyPathConnectedSpace W := (isOpen_Ioo : IsOpen W).locallyPathConnectedSpace
  let coordinate : AddCircle L ≃ₜ Circle := AddCircle.homeomorphCircle hL.ne'
  let circleTime : C(ℝ,Circle) :=
    ⟨fun t => coordinate (t:AddCircle L),coordinate.continuous.comp (AddCircle.continuous_mk' L)⟩
  have circleTime_period (t : ℝ) : circleTime (t+L)=circleTime t := by
    change coordinate (((t+L:ℝ):AddCircle L))=coordinate (t:AddCircle L)
    rw [AddCircle.coe_add,AddCircle.coe_period,add_zero]
  let strip : C(W × ℝ,E) :=
    ⟨fun wt => collar (wt.1,circleTime wt.2),
      collar.continuous.comp (continuous_fst.prodMk (circleTime.continuous.comp continuous_snd))⟩
  have hstart : p (dev.symm (verticalPath 0))=strip (zeroWidth,0) := (hcore 0).symm
  obtain ⟨F,⟨hFstart,hFprojection⟩,_⟩ :=
    hp.existsUnique_continuousMap_lifts strip (zeroWidth,0) (dev.symm (verticalPath 0)) hstart
  have hFcore (t : ℝ) : F (zeroWidth,t)=dev.symm (verticalPath t) := by
    have heq := hp.eq_of_comp_eq
      (F.continuous.comp (continuous_const.prodMk continuous_id))
      (dev.symm.continuous.comp verticalPath_isometry.continuous)
      (show (fun t : ℝ => p (F (zeroWidth,t)))=(fun t : ℝ => p (dev.symm (verticalPath t))) by
        funext t
        have h := congrFun hFprojection (zeroWidth,t)
        exact h.trans (hcore t)) 0 hFstart
    exact congrFun heq t
  have hFperiod (wt : W × ℝ) : F (wt.1,wt.2+L)=η (F wt) := by
    have heq := hp.eq_of_comp_eq
      (F.continuous.comp (continuous_fst.prodMk (continuous_snd.add continuous_const)))
      (η.continuous.comp F.continuous)
      (show (fun wt : W × ℝ => p (F (wt.1,wt.2+L)))=(fun wt : W × ℝ => p (η (F wt))) by
        funext wt
        rw [hη]
        have h1 := congrFun hFprojection (wt.1,wt.2+L)
        have h2 := congrFun hFprojection wt
        change p (F (wt.1,wt.2+L))=collar (wt.1,circleTime (wt.2+L)) at h1
        change p (F wt)=collar (wt.1,circleTime wt.2) at h2
        rw [circleTime_period] at h1
        exact h1.trans h2.symm) (zeroWidth,0) (by
          change F (zeroWidth,0+L)=η (F (zeroWidth,0))
          rw [zero_add,hFcore,hFcore,hperiod,zero_add])
    exact congrFun heq wt
  let f : ℝ → ℝ := fun t => (dev (F (positiveWidth,t))).re
  have hf : Continuous f :=
    UpperHalfPlane.continuous_re.comp (dev.continuous.comp
      (F.continuous.comp (continuous_const.prodMk continuous_id)))
  have hfzero (t : ℝ) : f t ≠ 0 := by
    intro hz
    let z := dev (F (positiveWidth,t))
    let u := Real.log z.im
    have hv : z=verticalPath u := by
      apply UpperHalfPlane.ext_re_im
      · exact hz
      · change z.im=Real.exp (Real.log z.im)
        exact (Real.exp_log z.im_pos).symm
    have he : collar (positiveWidth,circleTime t)=collar (zeroWidth,circleTime u) := by
      have hpF := congrFun hFprojection (positiveWidth,t)
      have hpaxis := hcore u
      have hlift : dev.symm (verticalPath u)=F (positiveWidth,t) := by
        rw [←hv]
        exact dev.symm_apply_apply _
      rw [hlift] at hpaxis
      exact hpF.symm.trans hpaxis.symm
    have hw := congrArg (fun wt : W × Circle => (wt.1:ℝ)) (hinj he)
    norm_num [positiveWidth,zeroWidth] at hw
  have hends : f L= -scale*f 0 := by
    change (dev (F (positiveWidth,L))).re= -scale*(dev (F (positiveWidth,0))).re
    have hp := hFperiod (positiveWidth,0)
    simp only [Prod.fst,Prod.snd,zero_add] at hp
    rw [hp]
    simpa only [dev.symm_apply_apply] using hflip (dev (F (positiveWidth,0)))
  have hzero : 0∈f '' Set.Icc (0:ℝ) L := by
    rcases lt_or_gt_of_ne (hfzero 0) with hneg | hpos
    · apply intermediate_value_Icc hL.le hf.continuousOn
      constructor
      · exact hneg.le
      · rw [hends]
        exact (mul_pos (neg_pos.mpr hneg) hscale).le.trans_eq (by ring)
    · apply intermediate_value_Icc' hL.le hf.continuousOn
      constructor
      · rw [hends]
        nlinarith
      · exact hpos.le
  obtain ⟨t,_,ht⟩ := hzero
  exact hfzero t ht

variable {E : Type} [TopologicalSpace E]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- The GIVEN circle loop follows an actual periodic locally unit-speed
geodesic up to a genuine circle homeomorphism. Angular time on Circle is
explicitly scaled by the positive length period. A nonminimal period is allowed, retaining multiply traversed classes.
At self-intersections the equation pins the traversal, not just its image. -/
def IsParametrizedClosedGeodesic [MetricSpace E] (h : C(Circle, E)) : Prop :=
  ∃ path : ℝ → E, ∃ period : ℝ, ∃ φ : Circle ≃ₜ Circle,
    0 < period ∧ Continuous path ∧
      (∀ t, path (t + period) = path t) ∧
      (∀ t, path t = h (φ (Circle.exp (2 * Real.pi * t / period)))) ∧
      ∀ t, ∃ ε : ℝ, 0 < ε ∧
        ∀ s u : ℝ, |s - t| < ε → |u - t| < ε →
          dist (path s) (path u) = |s - u|

/-- Corrected source Fact3.5(G1): both the produced loop and every competing
loop actually follow their geodesic parametrizations. Original f,H and
essential-loop hypotheses, simplicity implication and image uniqueness remain. -/
theorem closed_geodesic_exists_unique_parametrized_genus_two
    (H : ClosedHyperbolicMetric E) (f : C(Circle, E))
    (hessential : EssentialLoop f) (hE : IsGenus E 2) :
    letI : MetricSpace E := H.metric
    ∃ g : C(Circle, E),
      FreeHomotopic f g ∧ IsParametrizedClosedGeodesic g ∧
      (IsEmbedding f → IsEmbedding g) ∧
      ∀ h : C(Circle, E), FreeHomotopic f h →
        IsParametrizedClosedGeodesic h →
        Set.range h = Set.range g := by
  classical
  have ht2 : @T2Space E H.metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
    letI : MetricSpace E := H.metric
    infer_instance
  rw [H.compatible] at ht2
  letI : T2Space E := ht2
  let A := connectedComponent (f 1)
  have hfrange : Set.range f ⊆ A :=
    (isConnected_range f.continuous).subset_connectedComponent (Set.mem_range_self 1)
  let componentLoop : C(Circle,A) :=
    ⟨fun z => ⟨f z,hfrange (Set.mem_range_self z)⟩,f.continuous.subtype_mk _⟩
  letI : CompactSpace E := H.compact
  letI : CompactSpace A := isCompact_iff_compactSpace.mp isClosed_connectedComponent.isCompact
  letI : ConnectedSpace A := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  letI : LocallyConnectedSpace E := ChartedSpace.locallyConnectedSpace
    (EuclideanSpace ℝ (Fin 2)) E
  have haOpen : IsOpen A := isOpen_connectedComponent
  let U : TopologicalSpace.Opens E := ⟨A,haOpen⟩
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) A := TopologicalSpace.Opens.instChartedSpace U
  have actual_topological_universal_cover
      {S : Type} [TopologicalSpace S]
      [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [T2Space S] [CompactSpace S] [ConnectedSpace S] (x₀ : S) :
      ∃ t : TopologicalSpace (Σ z : S, Path.Homotopic.Quotient x₀ z),
        letI := t
        SecondCountableTopology (Σ z : S, Path.Homotopic.Quotient x₀ z) ∧
        T2Space (Σ z : S, Path.Homotopic.Quotient x₀ z) ∧
        Nonempty (ChartedSpace (EuclideanSpace ℝ (Fin 2))
          (Σ z : S, Path.Homotopic.Quotient x₀ z)) ∧
        SimplyConnectedSpace (Σ z : S, Path.Homotopic.Quotient x₀ z) ∧
        IsQuotientCoveringMap (Sigma.fst : (Σ z : S, Path.Homotopic.Quotient x₀ z) → S)
          (deck (Sigma.fst : (Σ z : S, Path.Homotopic.Quotient x₀ z) → S)) ∧
        Function.Surjective (Sigma.fst : (Σ z : S, Path.Homotopic.Quotient x₀ z) → S) ∧
        ∀ (c : Curve S) (hc : (⟨c.map, c.embedded.continuous⟩ : C(Circle, S)).Nullhomotopic),
          ∃ g : C(Circle, (Σ z : S, Path.Homotopic.Quotient x₀ z)),
            (∀ z, (g z).1 = c.map z) ∧ IsEmbedding g ∧ g.Nullhomotopic := by
    classical
    have hSCS : SecondCountableTopology S :=
      ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin 2)) S
    have hfull {S : Type} [TopologicalSpace S]
        [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [T2Space S] [CompactSpace S] [ConnectedSpace S] (x₀ : S) :
        ∃ t : TopologicalSpace (Σ z : S, Path.Homotopic.Quotient x₀ z),
          letI := t
          T2Space (Σ z : S, Path.Homotopic.Quotient x₀ z) ∧
          Nonempty (ChartedSpace (EuclideanSpace ℝ (Fin 2))
            (Σ z : S, Path.Homotopic.Quotient x₀ z)) ∧
          SimplyConnectedSpace (Σ z : S, Path.Homotopic.Quotient x₀ z) ∧
          IsQuotientCoveringMap (Sigma.fst : (Σ z : S, Path.Homotopic.Quotient x₀ z) → S)
            (deck (Sigma.fst : (Σ z : S, Path.Homotopic.Quotient x₀ z) → S)) ∧
          Function.Surjective (Sigma.fst : (Σ z : S, Path.Homotopic.Quotient x₀ z) → S) ∧
          ∀ (c : Curve S) (hc : (⟨c.map, c.embedded.continuous⟩ : C(Circle, S)).Nullhomotopic),
            ∃ g : C(Circle, (Σ z : S, Path.Homotopic.Quotient x₀ z)),
              (∀ z, (g z).1 = c.map z) ∧ IsEmbedding g ∧ g.Nullhomotopic := by
      classical
      have huniversal {S : Type} [TopologicalSpace S]
          [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ConnectedSpace S] (x₀ : S) :
          ∃ (U : S → Set S) (hi : ∀ i, i ∈ U i),
            (∀ i, IsOpen (U i)) ∧ (∀ i, ContractibleSpace (U i)) ∧
            ∃ (p : ∀ i, ∀ z : U i, Path ⟨i, hi i⟩ z)
              (t : TopologicalSpace (Σ z : S, Path.Homotopic.Quotient x₀ z)),
              letI := t
              IsCoveringMap (Sigma.fst : (Σ z : S, Path.Homotopic.Quotient x₀ z) → S) ∧
              SimplyConnectedSpace (Σ z : S, Path.Homotopic.Quotient x₀ z) ∧
              Function.Surjective (Sigma.fst : (Σ z : S, Path.Homotopic.Quotient x₀ z) → S) ∧
              IsLocalHomeomorph (Sigma.fst : (Σ z : S, Path.Homotopic.Quotient x₀ z) → S) ∧
              (∀ (i : S) (γ : Path.Homotopic.Quotient x₀ i),
                Continuous (fun z : U i => (⟨(z : S), γ.trans ((mk (p i z)).map
                  ⟨Subtype.val, continuous_subtype_val⟩)⟩ : Σ z : S, Path.Homotopic.Quotient x₀ z))) ∧
              ∀ (c : Curve S) (hc : (⟨c.map, c.embedded.continuous⟩ : C(Circle, S)).Nullhomotopic),
                ∃ g : C(Circle, (Σ z : S, Path.Homotopic.Quotient x₀ z)),
                  (∀ z, (g z).1 = c.map z) ∧
                  IsEmbedding g ∧ g.Nullhomotopic := by
        classical
        have hsurface {S : Type} [TopologicalSpace S]
            [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ConnectedSpace S] (x₀ : S) :
            ∃ (U : S → Set S) (hi : ∀ i, i ∈ U i),
              (∀ i, IsOpen (U i)) ∧ (∀ i, ContractibleSpace (U i)) ∧
              ∃ (p : ∀ i, ∀ z : U i, Path ⟨i, hi i⟩ z)
                (t : TopologicalSpace (Σ z : S, Path.Homotopic.Quotient x₀ z)),
                letI := t
                IsCoveringMap (Sigma.fst : (Σ z : S, Path.Homotopic.Quotient x₀ z) → S) ∧
                Function.Surjective (Sigma.fst : (Σ z : S, Path.Homotopic.Quotient x₀ z) → S) ∧
                IsLocalHomeomorph (Sigma.fst : (Σ z : S, Path.Homotopic.Quotient x₀ z) → S) ∧
                (∀ (i : S) (γ : Path.Homotopic.Quotient x₀ i),
                  Continuous (fun z : U i => (⟨(z : S), γ.trans ((mk (p i z)).map
                    ⟨Subtype.val, continuous_subtype_val⟩)⟩ : Σ z : S, Path.Homotopic.Quotient x₀ z))) ∧
                ∀ (c : Curve S) (hc : (⟨c.map, c.embedded.continuous⟩ : C(Circle, S)).Nullhomotopic),
                  ∃ g : C(Circle, (Σ z : S, Path.Homotopic.Quotient x₀ z)),
                    (∀ z, (g z).1 = c.map z) ∧
                    IsEmbedding g ∧ g.Nullhomotopic := by
          classical
          have hcover {S : Type} [TopologicalSpace S]
              [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
              (x₀ : S) (U : S → Set S) (hU : ∀ i, IsOpen (U i))
              [∀ i, ContractibleSpace (U i)] (hi : ∀ i, i ∈ U i)
              (q : ∀ i, Path x₀ i) (p : ∀ i, ∀ z : U i, Path ⟨i, hi i⟩ z) :
              ∃ t : TopologicalSpace (Σ z : S, Path.Homotopic.Quotient x₀ z),
                @IsCoveringMap (Σ z : S, Path.Homotopic.Quotient x₀ z) S t _ Sigma.fst ∧
                Function.Surjective (Sigma.fst : (Σ z : S, Path.Homotopic.Quotient x₀ z) → S) ∧
                ∀ (i : S) (γ : Path.Homotopic.Quotient x₀ i),
                  @Continuous (U i) (Σ z : S, Path.Homotopic.Quotient x₀ z) _ t
                    (fun z => ⟨(z : S), γ.trans ((mk (p i z)).map
                      ⟨Subtype.val, continuous_subtype_val⟩)⟩) := by
            classical
            have hcore {S : Type} [TopologicalSpace S]
                [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
                (x₀ : S) (U : S → Set S) (hU : ∀ i, IsOpen (U i))
                [∀ i, ContractibleSpace (U i)] (hi : ∀ i, i ∈ U i)
                (q : ∀ i, Path x₀ i) (p : ∀ i, ∀ z : U i, Path ⟨i, hi i⟩ z) :
                let F := Path.Homotopic.Quotient x₀ x₀
                let _ : TopologicalSpace F := ⊥
                let a : ∀ i z : S, Path.Homotopic.Quotient x₀ z := fun i z =>
                  if hz : z ∈ U i then (mk (q i)).trans ((mk (p i ⟨z, hz⟩)).map
                    ⟨Subtype.val, continuous_subtype_val⟩) else mk (q z)
                ∃ Z : FiberBundleCore S S F, Z.baseSet = U ∧
                  ∀ i j z v, Z.coordChange i j z v = v.trans ((a i z).trans (a j z).symm) := by
              classical
              have htransition {S : Type} [TopologicalSpace S]
                  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
                  (x₀ : S) (U V : Set S) (hU : IsOpen U) (hV : IsOpen V)
                  [ContractibleSpace U] [ContractibleSpace V]
                  (u : U) (v : V) (qU : Path.Homotopic.Quotient x₀ (u : S))
                  (qV : Path.Homotopic.Quotient x₀ (v : S))
                  (pU : ∀ z : U, Path u z) (pV : ∀ z : V, Path v z) :
                  IsLocallyConstant (fun z : ↥(U ∩ V) =>
                    (qU.trans ((mk (pU ⟨(z : S), z.property.1⟩)).map
                      ⟨Subtype.val, continuous_subtype_val⟩)).trans
                    (qV.trans ((mk (pV ⟨(z : S), z.property.2⟩)).map
                      ⟨Subtype.val, continuous_subtype_val⟩)).symm) := by
                classical
                have hcohere {S : Type} [TopologicalSpace S] (U W : Set S) [ContractibleSpace U]
                    (hWU : W ⊆ U) (u : U) (w z : W)
                    (p : Path u ⟨(w : S), hWU w.property⟩)
                    (r : Path u ⟨(z : S), hWU z.property⟩) (s : Path w z)
                    (x₀ : S) (q : Path.Homotopic.Quotient x₀ (u : S)) :
                    q.trans ((mk r).map ⟨Subtype.val, continuous_subtype_val⟩) =
                      (q.trans ((mk p).map ⟨Subtype.val, continuous_subtype_val⟩)).trans
                        ((mk s).map ⟨Subtype.val, continuous_subtype_val⟩) := by
                  let i : C(W, U) := ⟨fun z => ⟨(z : S), hWU z.property⟩, by fun_prop⟩
                  let j : C(U, S) := ⟨Subtype.val, continuous_subtype_val⟩
                  have hr : mk r = mk (p.trans (s.map i.continuous)) := Subsingleton.elim _ _
                  have hmap : (mk (p.trans (s.map i.continuous))).map j =
                      ((mk p).map j).trans ((mk s).map ⟨Subtype.val, continuous_subtype_val⟩) := by
                    change mk ((p.trans (s.map i.continuous)).map j.continuous) =
                      mk ((p.map j.continuous).trans (s.map continuous_subtype_val))
                    congr 1
                    ext t
                    simp only [Path.map_trans]
                    rfl
                  rw [hr, hmap, trans_assoc]
                have hcancel {S : Type} [TopologicalSpace S] {x₀ w z : S}
                    (a b : Path.Homotopic.Quotient x₀ w) (s : Path.Homotopic.Quotient w z) :
                    (a.trans s).trans (b.trans s).symm = a.trans b.symm := by
                  have hi : (b.trans s).symm = s.symm.trans b.symm := by
                    induction b using Quotient.ind
                    rename_i b
                    induction s using Quotient.ind
                    rename_i s
                    change mk (b.trans s).symm = mk (s.symm.trans b.symm)
                    rw [Path.trans_symm]
                  rw [hi, trans_assoc, ← trans_assoc s, trans_symm, refl_trans]
                rw [IsLocallyConstant.iff_exists_open]
                intro z
                obtain ⟨W, hzW, hW, hWUV, hcW⟩ :=
                  charted_surface_contractible_neighborhood (z : S) (U ∩ V) (hU.inter hV) z.property
                letI : ContractibleSpace W := hcW
                refine ⟨Subtype.val ⁻¹' W, hW.preimage continuous_subtype_val, hzW, ?_⟩
                intro z' hz'W
                let w : W := ⟨(z : S), hzW⟩
                let w' : W := ⟨(z' : S), hz'W⟩
                let s : Path w w' := PathConnectedSpace.somePath w w'
                let q : Path.Homotopic.Quotient (z : S) (z' : S) :=
                  (mk s).map ⟨Subtype.val, continuous_subtype_val⟩
                have hWU : W ⊆ U := fun y hy => (hWUV hy).1
                have hWV : W ⊆ V := fun y hy => (hWUV hy).2
                have ha := hcohere U W hWU u w w' (pU ⟨(z : S), z.property.1⟩)
                  (pU ⟨(z' : S), z'.property.1⟩) s x₀ qU
                have hb := hcohere V W hWV v w w' (pV ⟨(z : S), z.property.2⟩)
                  (pV ⟨(z' : S), z'.property.2⟩) s x₀ qV
                rw [ha, hb]
                exact hcancel _ _ q
              dsimp only
              let F := Path.Homotopic.Quotient x₀ x₀
              letI : TopologicalSpace F := ⊥
              letI : DiscreteTopology F := ⟨rfl⟩
              let a : ∀ i z : S, Path.Homotopic.Quotient x₀ z := fun i z =>
                if hz : z ∈ U i then (mk (q i)).trans ((mk (p i ⟨z, hz⟩)).map
                  ⟨Subtype.val, continuous_subtype_val⟩) else mk (q z)
              let k (i j z : S) : F := (a i z).trans (a j z).symm
              have hc (i j : S) : ContinuousOn (k i j) (U i ∩ U j) := by
                rw [continuousOn_iff_continuous_domRestrict]
                have hk := htransition x₀ (U i) (U j) (hU i) (hU j)
                  ⟨i, hi i⟩ ⟨j, hi j⟩ (mk (q i)) (mk (q j)) (p i) (p j)
                exact hk.continuous.congr (fun z => by simp [k, a, z.property.1, z.property.2])
              have hcancel {w : S} (b : Path.Homotopic.Quotient x₀ w)
                  (c d : Path.Homotopic.Quotient x₀ w) :
                  (b.trans c.symm).trans (c.trans d.symm) = b.trans d.symm := by
                rw [trans_assoc, ← trans_assoc c.symm, symm_trans, refl_trans]
              let Z : FiberBundleCore S S F := {
                baseSet := U
                isOpen_baseSet := hU
                indexAt := id
                mem_baseSet_at := hi
                coordChange := fun i j z v => v.trans (k i j z)
                coordChange_self := by
                  intro i z hz v
                  simp [k]
                continuousOn_coordChange := by
                  intro i j
                  have hkc : ContinuousOn (fun t : S × F => k i j t.1)
                      ((U i ∩ U j) ×ˢ univ) :=
                    (hc i j).comp continuous_fst.continuousOn (fun _ ht => ht.1)
                  have hop : Continuous (fun t : F × F => t.2.trans t.1) := continuous_of_discreteTopology
                  exact hop.comp_continuousOn (hkc.prodMk continuous_snd.continuousOn)
                coordChange_comp := by
                  intro i j l z hz v
                  change (v.trans (k i j z)).trans (k j l z) = v.trans (k i l z)
                  rw [trans_assoc]
                  congr 1
                  exact hcancel _ _ _ }
              exact ⟨Z, rfl, fun _ _ _ _ => rfl⟩
            let F := Path.Homotopic.Quotient x₀ x₀
            letI : TopologicalSpace F := ⊥
            letI : DiscreteTopology F := ⟨rfl⟩
            let a : ∀ i z : S, Path.Homotopic.Quotient x₀ z := fun i z =>
              if hz : z ∈ U i then (mk (q i)).trans ((mk (p i ⟨z, hz⟩)).map
                ⟨Subtype.val, continuous_subtype_val⟩) else mk (q z)
            obtain ⟨Z, hZU, hZc⟩ := hcore x₀ U hU hi q p
            let P := Σ z : S, Path.Homotopic.Quotient x₀ z
            let e : P ≃ Z.TotalSpace := {
              toFun := fun z => ⟨z.1, z.2.trans (a (Z.indexAt z.1) z.1).symm⟩
              invFun := fun z => ⟨z.1, z.2.trans (a (Z.indexAt z.1) z.1)⟩
              left_inv := by
                rintro ⟨z, γ⟩
                simp only [trans_assoc, symm_trans, trans_refl]
              right_inv := by
                rintro ⟨z, γ⟩
                change F at γ
                change (⟨z, ((γ : F).trans (a (Z.indexAt z) z)).trans
                  (a (Z.indexAt z) z).symm⟩ : Z.TotalSpace) = ⟨z, γ⟩
                congr 1
                rw [trans_assoc, trans_symm, trans_refl] }
            letI : TopologicalSpace P := TopologicalSpace.induced e inferInstance
            let E : P ≃ₜ Z.TotalSpace := e.toHomeomorphOfIsInducing (Topology.IsInducing.induced e)
            have hcover : IsCoveringMap Z.proj := FiberBundle.isCoveringMap
            refine ⟨inferInstance, ?_, ?_, ?_⟩
            · exact hcover.comp_homeomorph E
            · intro z
              exact ⟨⟨z, mk (q z)⟩, rfl⟩
            · intro i γ
              let v : F := γ.trans (mk (q i)).symm
              let g : U i → S × F := fun z => ((z : S), v)
              have hg : Continuous g := continuous_subtype_val.prodMk continuous_const
              have hgtr : ∀ z : U i, g z ∈ (Z.localTriv i).target := by
                intro z
                rw [Z.mem_localTriv_target, ← Z.baseSet_at, hZU]
                exact z.property
              have hG : Continuous (fun z : U i =>
                  E.symm ((Z.localTriv i).toOpenPartialHomeomorph.symm (g z))) :=
                E.symm.continuous.comp
                  ((Z.localTriv i).continuousOn_invFun.comp_continuous hg hgtr)
              apply hG.congr
              intro z
              change (⟨(z : S),
                (Z.coordChange i (Z.indexAt (z : S)) (z : S) v).trans
                  (a (Z.indexAt (z : S)) (z : S))⟩ : P) = _
              congr 1
              rw [hZc]
              change (v.trans ((a i (z : S)).trans (a (Z.indexAt (z : S)) (z : S)).symm)).trans
                (a (Z.indexAt (z : S)) (z : S)) = _
              simp only [trans_assoc, symm_trans, trans_refl]
              dsimp [v, a]
              rw [dite_eq_left z.property]
              rw [trans_assoc, ← trans_assoc (mk (q i)).symm, symm_trans, refl_trans]
          have hlocal (i : S) : ∃ A : Set S, i ∈ A ∧ IsOpen A ∧ ContractibleSpace A := by
            obtain ⟨A, hi, hA, _, hc⟩ :=
              charted_surface_contractible_neighborhood i univ isOpen_univ (mem_univ i)
            exact ⟨A, hi, hA, hc⟩
          choose U hi hU hc using hlocal
          letI : ∀ i, ContractibleSpace (U i) := hc
          let p : ∀ i, ∀ z : U i, Path ⟨i, hi i⟩ z :=
            fun i z => PathConnectedSpace.somePath ⟨i, hi i⟩ z
          letI : LocallyPathConnectedSpace S := ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) S
          letI : PathConnectedSpace S := PathConnectedSpace.of_locallyPathConnectedSpace
          let q : ∀ i, Path x₀ i := fun i => PathConnectedSpace.somePath x₀ i
          obtain ⟨t, hcov, hsurj, hsheet⟩ := hcover x₀ U hU hi q p
          refine ⟨U, hi, hU, hc, p, t, hcov, hsurj, hcov.isLocalHomeomorph, hsheet, ?_⟩
          letI := t
          intro c hnull
          obtain ⟨g, hpg, hg, hgn⟩ := exists_embedded_nullhomotopic_lift_of_covering
            Sigma.fst hcov hsurj c hnull
          refine ⟨g, ?_, hg, hgn⟩
          intro z
          exact congrArg (fun m : C(Circle, S) => m z) hpg
        have hsimply {S : Type} [TopologicalSpace S] (x₀ : S)
            (U : S → Set S) (hU : ∀ i, IsOpen (U i))
            [∀ i, ContractibleSpace (U i)] (hi : ∀ i, i ∈ U i)
            (p : ∀ i, ∀ z : U i, Path ⟨i, hi i⟩ z)
            [TopologicalSpace (Σ z : S, Path.Homotopic.Quotient x₀ z)]
            (hsheet : ∀ (i : S) (γ : Path.Homotopic.Quotient x₀ i),
              Continuous (fun z : U i => (⟨(z : S), γ.trans ((mk (p i z)).map
                ⟨Subtype.val, continuous_subtype_val⟩)⟩ : Σ z : S, Path.Homotopic.Quotient x₀ z)))
            (hcov : IsCoveringMap (Sigma.fst : (Σ z : S, Path.Homotopic.Quotient x₀ z) → S)) :
            SimplyConnectedSpace (Σ z : S, Path.Homotopic.Quotient x₀ z) := by
          classical
          have hcanonical {S : Type} [TopologicalSpace S] (x₀ : S)
              (U : S → Set S) (hU : ∀ i, IsOpen (U i))
              [∀ i, ContractibleSpace (U i)] (hi : ∀ i, i ∈ U i)
              (p : ∀ i, ∀ z : U i, Path ⟨i, hi i⟩ z)
              [TopologicalSpace (Σ z : S, Path.Homotopic.Quotient x₀ z)]
              (hsheet : ∀ (i : S) (γ : Path.Homotopic.Quotient x₀ i),
                Continuous (fun z : U i => (⟨(z : S), γ.trans ((mk (p i z)).map
                  ⟨Subtype.val, continuous_subtype_val⟩)⟩ : Σ z : S, Path.Homotopic.Quotient x₀ z)))
              (α : C(unitInterval, S)) (γ : Path.Homotopic.Quotient x₀ (α 0)) :
              ∃ L : C(unitInterval, (Σ z : S, Path.Homotopic.Quotient x₀ z)),
                (∀ t, (L t).1 = α t) ∧ L 0 = ⟨α 0, γ⟩ ∧
                L 1 = ⟨α 1, γ.trans ((mk Path.id).map α)⟩ := by
            classical
            have hcont {S : Type} [TopologicalSpace S] (x₀ : S)
                (U : S → Set S) (hU : ∀ i, IsOpen (U i))
                [∀ i, ContractibleSpace (U i)] (hi : ∀ i, i ∈ U i)
                (p : ∀ i, ∀ z : U i, Path ⟨i, hi i⟩ z)
                [TopologicalSpace (Σ z : S, Path.Homotopic.Quotient x₀ z)]
                (hsheet : ∀ (i : S) (γ : Path.Homotopic.Quotient x₀ i),
                  Continuous (fun z : U i => (⟨(z : S), γ.trans ((mk (p i z)).map
                    ⟨Subtype.val, continuous_subtype_val⟩)⟩ : Σ z : S, Path.Homotopic.Quotient x₀ z)))
                (α : C(unitInterval, S)) (γ : Path.Homotopic.Quotient x₀ (α 0)) :
                letI : ContractibleSpace unitInterval :=
                  (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩
                Continuous (fun t : unitInterval =>
                  (⟨α t, γ.trans ((mk (PathConnectedSpace.somePath (0 : unitInterval) t)).map α)⟩ :
                    Σ z : S, Path.Homotopic.Quotient x₀ z)) := by
              classical
              letI : ContractibleSpace unitInterval :=
                (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩
              letI : LocallyPathConnectedSpace unitInterval :=
                (isQuotientMap_projIcc (a := (0 : ℝ)) (b := 1) (h := by norm_num)).locallyPathConnectedSpace
              let η (t : unitInterval) := (mk (PathConnectedSpace.somePath (0 : unitInterval) t)).map α
              let Γ (t : unitInterval) : Σ z : S, Path.Homotopic.Quotient x₀ z := ⟨α t, γ.trans (η t)⟩
              change Continuous Γ
              rw [continuous_iff_continuousAt]
              intro t₀
              let i := α t₀
              let A := α ⁻¹' U i
              have hA : IsOpen A := (hU i).preimage α.continuous
              have htA : t₀ ∈ A := hi i
              let J := pathComponentIn A t₀
              have hJ : IsOpen J := hA.pathComponentIn t₀
              have htJ : t₀ ∈ J := mem_pathComponentIn_self htA
              have hJA : J ⊆ A := pathComponentIn_subset
              have hJP : IsPathConnected J := isPathConnected_pathComponentIn htA
              let β : J → U i := fun t => ⟨α t, hJA t.property⟩
              have hβ : Continuous β := by fun_prop
              have hΓJ : Continuous (fun t : J => Γ t) := by
                apply ((hsheet i (γ.trans (η t₀))).comp hβ).congr
                intro t
                obtain ⟨s, hs⟩ := hJP.joinedIn t₀ htJ t t.property
                have hη : η (t : unitInterval) = (η t₀).trans ((mk s).map α) := by
                  have hp : mk (PathConnectedSpace.somePath (0 : unitInterval) (t : unitInterval)) =
                      mk ((PathConnectedSpace.somePath (0 : unitInterval) t₀).trans s) := Subsingleton.elim _ _
                  dsimp [η]
                  rw [hp]
                  change mk (((PathConnectedSpace.somePath (0 : unitInterval) t₀).trans s).map α.continuous) =
                    mk (((PathConnectedSpace.somePath (0 : unitInterval) t₀).map α.continuous).trans
                      (s.map α.continuous))
                  congr 1
                  exact Path.map_trans _ _ _
                let l : Path ⟨i, hi i⟩ (β t) := {
                  toFun := fun v => ⟨α (s v), hJA (hs v)⟩
                  continuous_toFun := by fun_prop
                  source' := by apply Subtype.ext; exact congrArg α s.source
                  target' := by apply Subtype.ext; exact congrArg α s.target }
                have hl : mk (p i (β t)) = mk l := Subsingleton.elim _ _
                have hlmap : (mk l).map ⟨Subtype.val, continuous_subtype_val⟩ = (mk s).map α := by
                  change mk (l.map continuous_subtype_val) = mk (s.map α.continuous)
                  rfl
                change (⟨α t, (γ.trans (η t₀)).trans
                  ((mk (p i (β t))).map ⟨Subtype.val, continuous_subtype_val⟩)⟩ :
                  Σ z : S, Path.Homotopic.Quotient x₀ z) = Γ t
                rw [hl, hlmap]
                dsimp [Γ]
                congr 1
                rw [hη, trans_assoc]
              have hΓon : ContinuousOn Γ J := continuousOn_iff_continuous_domRestrict.mpr hΓJ
              exact hΓon.continuousAt (hJ.mem_nhds htJ)
            letI : ContractibleSpace unitInterval :=
              (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩
            let L : C(unitInterval, (Σ z : S, Path.Homotopic.Quotient x₀ z)) :=
              ⟨fun t => ⟨α t, γ.trans ((mk (PathConnectedSpace.somePath (0 : unitInterval) t)).map α)⟩,
                hcont x₀ U hU hi p hsheet α γ⟩
            refine ⟨L, fun _ => rfl, ?_, ?_⟩
            · have hz : mk (PathConnectedSpace.somePath (0 : unitInterval) 0) =
                  Path.Homotopic.Quotient.refl 0 := Subsingleton.elim _ _
              change (⟨α 0, γ.trans ((mk (PathConnectedSpace.somePath (0 : unitInterval) 0)).map α)⟩ :
                Σ z : S, Path.Homotopic.Quotient x₀ z) = _
              rw [hz]
              have hmap : (Path.Homotopic.Quotient.refl (0 : unitInterval)).map α =
                  Path.Homotopic.Quotient.refl (α 0) := rfl
              rw [hmap, trans_refl]
            · have ho : mk (PathConnectedSpace.somePath (0 : unitInterval) 1) = mk Path.id :=
                  Subsingleton.elim _ _
              change (⟨α 1, γ.trans ((mk (PathConnectedSpace.somePath (0 : unitInterval) 1)).map α)⟩ :
                Σ z : S, Path.Homotopic.Quotient x₀ z) = _
              rw [ho]
          have hpc : PathConnectedSpace (Σ z : S, Path.Homotopic.Quotient x₀ z) := by
            let P := Σ z : S, Path.Homotopic.Quotient x₀ z
            let root : P := ⟨x₀, Path.Homotopic.Quotient.refl x₀⟩
            have hroot (y : P) : Joined root y := by
              rcases y with ⟨z, η⟩
              obtain ⟨q⟩ := η
              let α : C(unitInterval, S) := q.toContinuousMap
              let γ : Path.Homotopic.Quotient x₀ (α 0) :=
                (Path.Homotopic.Quotient.refl x₀).cast rfl q.source
              obtain ⟨L, hproj, hz, ho⟩ := hcanonical x₀ U hU hi p hsheet α γ
              have hzero : L 0 = root := by
                rw [hz]
                apply Sigma.ext q.source
                exact Path.Homotopic.Quotient.cast_heq (γ := Path.Homotopic.Quotient.refl x₀) rfl q.source
              have hclass : HEq (γ.trans ((mk Path.id).map α)) (mk q) := by
                change HEq (mk (((Path.refl x₀).cast rfl q.source).trans (Path.id.map α.continuous))) (mk q)
                have he : HEq (mk (((Path.refl x₀).cast rfl q.source).trans (Path.id.map α.continuous)))
                    (mk ((Path.refl x₀).trans q)) := Path.Homotopic.hpath_hext (fun _ => rfl)
                apply he.trans
                apply heq_of_eq
                rw [mk_trans, mk_refl, refl_trans]
              have hone : L 1 = ⟨z, mk q⟩ := by
                rw [ho]
                exact Sigma.ext q.target hclass
              exact ⟨⟨L, hzero, hone⟩⟩
            exact ⟨⟨root⟩, fun x y => (hroot x).symm.trans (hroot y)⟩
          rw [simply_connected_iff_loops_nullhomotopic]
          refine ⟨hpc, ?_⟩
          rintro ⟨w, η⟩ δ
          obtain ⟨q⟩ := η
          let x : Σ z : S, Path.Homotopic.Quotient x₀ z := ⟨w, mk q⟩
          let α : Path w w := δ.map hcov.continuous
          let γ : Path.Homotopic.Quotient x₀ (α 0) := (mk q).cast rfl α.source
          obtain ⟨L, hproj, hz, ho⟩ := hcanonical x₀ U hU hi p hsheet α.toContinuousMap γ
          have hzero : L 0 = x := by
            rw [hz]
            apply Sigma.ext α.source
            exact Path.Homotopic.Quotient.cast_heq (γ := mk q) rfl α.source
          have hsame : (L : unitInterval → (Σ z : S, Path.Homotopic.Quotient x₀ z)) = δ :=
            hcov.eq_of_comp_eq L.continuous δ.continuous (funext hproj) 0
              (hzero.trans δ.source.symm)
          have hone : L 1 = x := by rw [hsame]; exact δ.target
          have hh : HEq (γ.trans ((mk Path.id).map α.toContinuousMap)) (mk q) :=
            (Sigma.mk.inj_iff.mp (ho.symm.trans hone)).2
          have he : HEq (γ.trans ((mk Path.id).map α.toContinuousMap)) ((mk q).trans (mk α)) := by
            change HEq (mk ((q.cast rfl α.source).trans (Path.id.map α.continuous))) (mk (q.trans α))
            exact Path.Homotopic.hpath_hext (fun _ => rfl)
          have heq : (mk q).trans (mk α) = mk q := eq_of_heq (he.symm.trans hh)
          have hα : mk α = Path.Homotopic.Quotient.refl w := by
            have hc := congrArg (fun r : Path.Homotopic.Quotient x₀ w => (mk q).symm.trans r) heq
            simpa only [← trans_assoc, symm_trans, refl_trans] using hc
          apply Path.Homotopic.Quotient.eq.mp
          apply hcov.injective_path_homotopic_map
          change mk α = Path.Homotopic.Quotient.refl w
          exact hα
        obtain ⟨U, hi, hU, hc, p, t, hcov, hsurj, hloc, hsheet, hlift⟩ := hsurface x₀
        letI := t
        letI : ∀ i, ContractibleSpace (U i) := hc
        have hsc := hsimply x₀ U hU hi p hsheet hcov
        exact ⟨U, hi, hU, hc, p, t, hcov, hsc, hsurj, hloc, hsheet, hlift⟩
      have hgeometry {S E : Type} [TopologicalSpace S] [TopologicalSpace E] [T2Space S]
          [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
          (p : E → S) (hp : IsCoveringMap p) :
          T2Space E ∧ Nonempty (ChartedSpace (EuclideanSpace ℝ (Fin 2)) E) := by
        classical
        have ht : T2Space E := by
          refine ⟨fun x y hxy => ?_⟩
          by_cases hpxy : p x = p y
          · exact hp.isSeparatedMap x y hpxy hxy
          · obtain ⟨U,V,hU,hV,hx,hy,hUV⟩ := t2_separation hpxy
            exact ⟨p ⁻¹' U,p ⁻¹' V,hU.preimage hp.continuous,hV.preimage hp.continuous,
              hx,hy,hUV.preimage p⟩
        let c (x : E) : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin 2)) :=
          (hp.isLocalHomeomorph.localInverseAt x).symm.trans
            (chartAt (EuclideanSpace ℝ (Fin 2)) (p x))
        have hmem (x : E) : x ∈ (c x).source := by
          change x ∈ (hp.isLocalHomeomorph.localInverseAt x).target ∧
            (hp.isLocalHomeomorph.localInverseAt x).symm x ∈
              (chartAt (EuclideanSpace ℝ (Fin 2)) (p x)).source
          refine ⟨hp.isLocalHomeomorph.self_mem_localInverseAt_target, ?_⟩
          rw [hp.isLocalHomeomorph.localInverseAt_symm]
          exact mem_chart_source (EuclideanSpace ℝ (Fin 2)) (p x)
        exact ⟨ht, ⟨{
          atlas := range c
          chartAt := c
          mem_chart_source := hmem
          chart_mem_atlas := fun x => ⟨x,rfl⟩ }⟩⟩
      have hdeck {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
          [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
          (p : E → S) (hp : IsCoveringMap p) (hsurj : Function.Surjective p) :
          IsQuotientCoveringMap p (deck p) := by
        classical
        have htrans (e e' : E) (he : p e' = p e) : ∃ g : deck p, g • e = e' := by
          let f : C(E, S) := ⟨p, hp.continuous⟩
          obtain ⟨F, hF, _⟩ := hp.existsUnique_continuousMap_lifts f e e' he
          obtain ⟨G, hG, _⟩ := hp.existsUnique_continuousMap_lifts f e' e he.symm
          have hGF : (G.comp F : E → E) = id := by
            apply hp.eq_of_comp_eq (G.comp F).continuous continuous_id
            · funext x
              exact (congrFun hG.2 (F x)).trans (congrFun hF.2 x)
            · exact (congrArg G hF.1).trans hG.1
          have hFG : (F.comp G : E → E) = id := by
            apply hp.eq_of_comp_eq (F.comp G).continuous continuous_id
            · funext x
              exact (congrFun hF.2 (G x)).trans (congrFun hG.2 x)
            · exact (congrArg F hG.1).trans hF.1
          let H : E ≃ₜ E := {
            toFun := F
            invFun := G
            left_inv := congrFun hGF
            right_inv := congrFun hFG
            continuous_toFun := F.continuous
            continuous_invFun := G.continuous }
          exact ⟨⟨H,hF.2⟩,hF.1⟩
        refine { hp.isQuotientMap hsurj, (inferInstance : ContinuousConstSMul (deck p) E) with
          apply_eq_iff_mem_orbit := ?_
          disjoint := ?_ }
        · intro e e'
          constructor
          · intro he
            exact htrans e' e he
          · rintro ⟨g, rfl⟩
            exact deck.proj_smul g e'
        · intro e
          obtain ⟨h, he, hph⟩ := hp.isLocalHomeomorph e
          refine ⟨h.source,h.open_source.mem_nhds he,?_⟩
          intro g hmeet
          obtain ⟨z, ⟨⟨y,hy,rfl⟩,hgy⟩⟩ := hmeet
          have hfix : g • y = y := by
            apply h.injOn hgy hy
            rw [← hph]
            exact deck.proj_smul g y
          have heq : ((g : E ≃ₜ E) : E → E) = id :=
            hp.eq_of_comp_eq (g : E ≃ₜ E).continuous continuous_id (deck.comp_eq g) y hfix
          apply Subtype.ext
          apply Homeomorph.ext
          exact congrFun heq
      obtain ⟨U, hi, hU, hc, p, t, hcov, hsc, hsurj, hloc, hsheet, hlift⟩ := huniversal x₀
      letI := t
      let P := Σ z : S, Path.Homotopic.Quotient x₀ z
      obtain ⟨ht2, ⟨cs⟩⟩ := hgeometry (Sigma.fst : P → S) hcov
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) P := cs
      letI : LocallyPathConnectedSpace P :=
        ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) P
      letI : SimplyConnectedSpace P := hsc
      have hqc := hdeck (Sigma.fst : P → S) hcov hsurj
      exact ⟨t, ht2, ⟨cs⟩, hsc, hqc, hsurj, hlift⟩
    have hsecond {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
        [SecondCountableTopology S] [PathConnectedSpace E]
        (p : E → S) (hp : IsCoveringMap p) (hsurj : Function.Surjective p) :
        SecondCountableTopology E := by
      classical
      have hcount {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
          [SecondCountableTopology S] [PathConnectedSpace E]
          (p : E → S) (hp : IsCoveringMap p) (e : E) : Countable (p ⁻¹' {p e}) := by
        classical
        let A := Path (p e) (p e)
        letI : SecondCountableTopology A :=
          (Topology.IsInducing.induced (fun γ : A => γ.toContinuousMap)).secondCountableTopology
        let H : C(unitInterval × A, S) := ⟨fun ta => ta.2 ta.1, by fun_prop⟩
        let f : C(A, E) := ContinuousMap.const A e
        have hz : ∀ γ : A, H (0, γ) = p (f γ) := fun γ => γ.source
        let K := hp.liftHomotopy H f hz
        have hk (γ : A) : p (K (1, γ)) = p e :=
          (congrFun (hp.liftHomotopy_lifts H f hz) (1, γ)).trans γ.target
        let L : A → p ⁻¹' {p e} := fun γ => ⟨K (1, γ), hk γ⟩
        have hLc : Continuous L := by
          exact (K.continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk hk
        have hLs : Function.Surjective L := by
          intro y
          let Γ := PathConnectedSpace.somePath e (y : E)
          let γ : A := (Γ.map hp.continuous).cast rfl y.property.symm
          have hsame : (fun t : unitInterval => K (t, γ)) = Γ := by
            apply hp.eq_of_comp_eq
              (K.continuous.comp (continuous_id.prodMk continuous_const)) Γ.continuous
            · funext t
              exact congrFun (hp.liftHomotopy_lifts H f hz) (t, γ)
            · exact (hp.liftHomotopy_zero H f hz γ).trans Γ.source.symm
          refine ⟨γ, ?_⟩
          apply Subtype.ext
          exact (congrFun hsame 1).trans Γ.target
        letI : DiscreteTopology (p ⁻¹' {p e}) := (hp (p e)).discreteTopology_fiber
        letI : SeparableSpace (p ⁻¹' {p e}) := hLs.denseRange.separableSpace hLc
        exact separableSpace_iff_countable.mp inferInstance
      letI (x : S) : Countable (p ⁻¹' {x}) := by
        obtain ⟨e,rfl⟩ := hsurj x
        exact hcount p hp e
      letI (x : S) : DiscreteTopology (p ⁻¹' {x}) := (hp x).discreteTopology_fiber
      letI (x : S) : Nonempty (p ⁻¹' {x}) := by
        obtain ⟨e,he⟩ := hsurj x
        exact ⟨⟨e,he⟩⟩
      let t (x : S) : Trivialization (p ⁻¹' {x}) p := (hp x).toTrivialization
      have hsource (x : S) : SecondCountableTopology (t x).source :=
        (t x).toOpenPartialHomeomorph.secondCountableTopology_source
      obtain ⟨r,hr,hbase⟩ := isLindelof_univ.elim_countable_subcover
        (fun x : S => (t x).baseSet) (fun x => (t x).open_baseSet) (by
          intro x _
          exact mem_iUnion.mpr ⟨x,(hp x).mem_toTrivialization_baseSet⟩)
      letI := hr.toEncodable
      letI (i : r) : SecondCountableTopology (t (i : S)).source := hsource i
      have hcover : ⋃ i : r, (t (i : S)).source = univ := by
        apply eq_univ_of_forall
        intro e
        obtain ⟨i,hi,he⟩ := mem_iUnion₂.mp (hbase (mem_univ (p e)))
        exact mem_iUnion.mpr ⟨⟨i,hi⟩,(t i).mem_source.mpr he⟩
      exact secondCountableTopology_of_countable_cover (fun i : r => (t (i : S)).open_source) hcover
    obtain ⟨t,ht2,hcharts,hsc,hqc,hsurj,hlift⟩ := hfull x₀
    letI := t
    let P := Σ z : S, Path.Homotopic.Quotient x₀ z
    letI : SecondCountableTopology S := hSCS
    letI : SimplyConnectedSpace P := hsc
    have hsecondP := hsecond (Sigma.fst : P → S) hqc.isCoveringMap hsurj
    exact ⟨t,hsecondP,ht2,hcharts,hsc,hqc,hsurj,hlift⟩
  let base : A := ⟨f 1,mem_connectedComponent⟩
  obtain ⟨t,hsecond,hcoverT2,hcharts,hsc,hqc,hsurj,hlift⟩ := actual_topological_universal_cover base
  let P := Σ z : A, Path.Homotopic.Quotient base z
  letI : TopologicalSpace P := t
  letI : SecondCountableTopology P := hsecond
  letI : T2Space P := hcoverT2
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) P := hcharts.some
  letI : SimplyConnectedSpace P := hsc
  have actual_cover_plane : Nonempty (Schoenflies.Plane ≃ₜ P) :=
    actual_hyperbolic_component_simply_connected_cover_is_plane H (f 1) Sigma.fst
      hqc.isCoveringMap hsurj
  have actual_circle_lift_impossible (lift : C(Circle,P))
      (hlift : ∀ z, (lift z).1.val = f z) : False := by
    obtain ⟨plane⟩ := actual_cover_plane
    have hprojection : Continuous (fun z : P => z.1.val) :=
      continuous_subtype_val.comp hqc.isCoveringMap.continuous
    let contraction : C(Circle × Interval,E) :=
      ⟨fun zt => (plane ((1 - zt.2.val) • plane.symm (lift zt.1))).1.val,
        hprojection.comp (plane.continuous.comp
          ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).smul
            (plane.symm.continuous.comp (lift.continuous.comp continuous_fst))))⟩
    apply hessential
    refine ⟨(plane 0).1.val,contraction,?_,?_⟩
    · intro z
      change (plane ((1 - (0 : ℝ)) • plane.symm (lift z))).1.val = f z
      simpa using hlift z
    · intro z
      change (plane ((1 - (1 : ℝ)) • plane.symm (lift z))).1.val = (plane 0).1.val
      simp
  let circleCoordinate : AddCircle (1 : ℝ) ≃ₜ Circle :=
    AddCircle.homeomorphCircle one_ne_zero
  let periodicLoop : C(ℝ,A) :=
    componentLoop.comp ⟨fun t : ℝ => circleCoordinate (t : AddCircle (1 : ℝ)),
      circleCoordinate.continuous.comp (AddCircle.continuous_mk' 1)⟩
  have periodicLoop_period (t : ℝ) : periodicLoop (t + 1) = periodicLoop t := by
    change componentLoop (circleCoordinate ((t + 1 : ℝ) : AddCircle (1 : ℝ))) = _
    rw [AddCircle.coe_add_period]
    rfl
  obtain ⟨initialLift,initialLift_projection⟩ := hsurj (periodicLoop 0)
  obtain ⟨liftedPeriodicLoop,hliftedPeriodicLoop,huniqueLift⟩ :=
    hqc.isCoveringMap.existsUnique_continuousMap_lifts periodicLoop 0 initialLift
      initialLift_projection
  have liftedPeriodicLoop_projection (t : ℝ) :
      (liftedPeriodicLoop t).1 = periodicLoop t := by
    exact congrFun hliftedPeriodicLoop.2 t
  have liftedPeriodicLoop_endpoints_ne : liftedPeriodicLoop 0 ≠ liftedPeriodicLoop 1 := by
    intro hend
    let circleLift : C(Circle,P) :=
      ⟨fun z => AddCircle.liftIco 1 0 liftedPeriodicLoop (circleCoordinate.symm z),
        (AddCircle.liftIco_zero_continuous hend
          liftedPeriodicLoop.continuous.continuousOn).comp circleCoordinate.symm.continuous⟩
    apply actual_circle_lift_impossible circleLift
    intro z
    change (liftedPeriodicLoop ((AddCircle.equivIco 1 0) (circleCoordinate.symm z))).1.val = f z
    rw [liftedPeriodicLoop_projection]
    change f (circleCoordinate (((AddCircle.equivIco 1 0)
      (circleCoordinate.symm z) : ℝ) : AddCircle (1 : ℝ))) = f z
    rw [AddCircle.coe_equivIco, circleCoordinate.apply_symm_apply]
  have lifted_period_end_projection :
      (liftedPeriodicLoop 1).1 = (liftedPeriodicLoop 0).1 := by
    rw [liftedPeriodicLoop_projection,liftedPeriodicLoop_projection]
    simpa using periodicLoop_period 0
  obtain ⟨deckTranslation,hdeckTranslation⟩ :=
    hqc.apply_eq_iff_mem_orbit.mp lifted_period_end_projection
  have deckTranslation_ne_one : deckTranslation ≠ 1 := by
    intro hdeck
    apply liftedPeriodicLoop_endpoints_ne
    simpa [hdeck] using hdeckTranslation
  have liftedPeriodicLoop_deck_period (t : ℝ) :
      liftedPeriodicLoop (t + 1) = deckTranslation • liftedPeriodicLoop t := by
    have heq : (fun t : ℝ => liftedPeriodicLoop (t + 1)) =
        (fun t : ℝ => deckTranslation • liftedPeriodicLoop t) :=
      hqc.isCoveringMap.eq_of_comp_eq
        (liftedPeriodicLoop.continuous.comp (continuous_id.add continuous_const))
        (hqc.continuous_const_smul deckTranslation |>.comp liftedPeriodicLoop.continuous)
        (by
          funext t
          change (liftedPeriodicLoop (t + 1)).1 =
            (deckTranslation • liftedPeriodicLoop t).1
          rw [hqc.map_smul,liftedPeriodicLoop_projection,
            liftedPeriodicLoop_projection,periodicLoop_period])
        0 (by simpa using hdeckTranslation.symm)
    exact congrFun heq t
  let sourceComponentMetric : MetricSpace A := MetricSpace.induced Subtype.val Subtype.val_injective H.metric
  have sourceComponentMetric_topology :
      sourceComponentMetric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
        (inferInstance : TopologicalSpace A) := by
    change TopologicalSpace.induced Subtype.val
      H.metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      TopologicalSpace.induced Subtype.val (inferInstance : TopologicalSpace E)
    rw [H.compatible]
  letI : MetricSpace A := sourceComponentMetric.replaceTopology sourceComponentMetric_topology.symm
  have fiber_nonempty (a : A) : Nonempty ((Sigma.fst : P → A) ⁻¹' {a}) := by
    obtain ⟨z,hz⟩ := hsurj a
    exact ⟨⟨z,hz⟩⟩
  letI (a : A) : Nonempty ((Sigma.fst : P → A) ⁻¹' {a}) := fiber_nonempty a
  have actualCoveringMap : IsCoveringMap (Sigma.fst : P → A) := hqc.isCoveringMap
  let actualTrivialization (a : A) := (actualCoveringMap a).toTrivialization
  have actualTrivialization_base (a : A) : a ∈ (actualTrivialization a).baseSet :=
    (actualCoveringMap a).mem_toTrivialization_baseSet
  have uniform_evenly_covered_radius : ∃ ε : ℝ, 0 < ε ∧ ∀ x : A,
      ∃ a : A, Metric.ball x ε ⊆ (actualTrivialization a).baseSet := by
    obtain ⟨ε,hε,hcover⟩ := lebesgue_number_lemma_of_metric isCompact_univ
      (fun a => (actualTrivialization a).open_baseSet)
      (show Set.univ ⊆ ⋃ a, (actualTrivialization a).baseSet from
        fun x _ => Set.mem_iUnion.mpr ⟨x,actualTrivialization_base x⟩)
    exact ⟨ε,hε,fun x => hcover x (Set.mem_univ x)⟩
  obtain ⟨development,development_metric⟩ :=
    actual_hyperbolic_component_simply_connected_cover_develops H (f 1)
      (Sigma.fst : P → A) actualCoveringMap hsurj
  have actual_deck_development_isometric (η : P ≃ₜ P)
      (hη : ∀ x : P, (η x).1 = x.1) :
      Isometry ((development.symm.trans η).trans development) := by
    exact @actual_deck_development_isometry E P H.metric t
      (fun x : P => x.1.val) development development_metric η
      (fun x => congrArg Subtype.val (hη x))
  let geometricDeck : H2 ≃ₜ H2 :=
    (development.symm.trans deckTranslation.val).trans development
  have deckTranslation_no_fixed_point (x : P) : deckTranslation • x ≠ x := by
    intro hx
    have := hqc.isCancelSMul
    apply deckTranslation_ne_one
    exact IsCancelSMul.right_cancel _ _ x (by simpa using hx)
  have geometricDeck_no_fixed_point (z : H2) : geometricDeck z ≠ z := by
    intro hz
    apply deckTranslation_no_fixed_point (development.symm z)
    apply development.injective
    change development (deckTranslation • development.symm z) =
      development (development.symm z)
    simpa only [geometricDeck,Homeomorph.trans_apply,Homeomorph.symm_apply_apply,
      development.apply_symm_apply,Subgroup.smul_def,Homeomorph.smul_def] using hz
  have geometricDeck_locally_isometric (x : H2) :
      ∃ W : Set H2, IsOpen W ∧ x ∈ W ∧
        ∀ y ∈ W, ∀ z ∈ W, dist (geometricDeck y) (geometricDeck z) = dist y z := by
    obtain ⟨U,hU,hxU,hmetricU⟩ := development_metric (development.symm x)
    obtain ⟨V,hV,hxV,hmetricV⟩ := development_metric
      (deckTranslation • development.symm x)
    let W := development.symm ⁻¹' (U ∩ deckTranslation.val ⁻¹' V)
    have hW : IsOpen W :=
      (hU.inter (hV.preimage deckTranslation.val.continuous)).preimage
        development.symm.continuous
    refine ⟨W,hW,⟨hxU,hxV⟩,?_⟩
    intro y hy z hz
    change dist (development (deckTranslation • development.symm y))
      (development (deckTranslation • development.symm z)) = dist y z
    rw [← hmetricV (deckTranslation • development.symm y) hy.2
      (deckTranslation • development.symm z) hz.2]
    have hyproj : (deckTranslation • development.symm y).1.val =
        (development.symm y).1.val := congrArg Subtype.val (hqc.map_smul deckTranslation)
    have hzproj : (deckTranslation • development.symm z).1.val =
        (development.symm z).1.val := congrArg Subtype.val (hqc.map_smul deckTranslation)
    rw [hyproj,hzproj,hmetricU _ hy.1 _ hz.1]
    rw [development.apply_symm_apply,development.apply_symm_apply]
  have zero_eq_I : verticalPath 0 = UpperHalfPlane.I := by
    apply UpperHalfPlane.ext_re_im <;> simp [verticalPath]
  have vertical_radius_sphere (r : ℝ) (hr : 0 ≤ r) (z : H2)
      (h : dist UpperHalfPlane.I z = r) :
      Real.exp r * (z.re ^ 2 + z.im ^ 2 + 1) =
        z.im * (1 + (Real.exp r) ^ 2) := by
    have hstd : dist (verticalPath 0) (verticalPath r) = r := by
      simpa [Real.dist_eq,abs_of_nonneg hr,abs_of_nonpos (neg_nonpos.mpr hr)] using
        verticalPath_isometry.dist_eq 0 r
    have hc := congrArg Real.cosh (h.trans (zero_eq_I ▸ hstd).symm)
    rw [UpperHalfPlane.cosh_dist',UpperHalfPlane.cosh_dist'] at hc
    simp only [verticalPath,UpperHalfPlane.mk_re,UpperHalfPlane.mk_im] at hc
    simp only [UpperHalfPlane.I_re,UpperHalfPlane.I_im,zero_sub,neg_sq,
      one_pow,zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hc
    field_simp at hc
    nlinarith [hc]
  have denominator_nonzero (a b : ℝ) (hab : 0 < a^2+b^2) (w : H2) :
      (-(b : ℂ) * (w : ℂ) + a) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp [Complex.mul_im] at him
    have hb : b = 0 := by
      rcases him with hb | hw
      · exact hb
      · exact (w.im_pos.ne' hw).elim
    have ha : a ≠ 0 := by
      intro ha
      rw [ha,hb] at hab
      norm_num at hab
    exact ha (by simpa [hb] using h)
  have rotation_maps_vertical_radius (r : ℝ) (hr : 0 ≤ r) (z : H2)
      (h : dist UpperHalfPlane.I z = r)
      (hab : 0 < (1-Real.exp r*z.im)^2+z.re^2) :
      (stabilizerRotation (1-Real.exp r*z.im) z.re hab • verticalPath r : H2) = z := by
    let a := 1-Real.exp r*z.im
    let b := z.re
    have hsphere := vertical_radius_sphere r hr z h
    have hEim : (Complex.exp (r : ℂ)).im = 0 := by
      simpa using Complex.exp_ofReal_im r
    have hEre : (Complex.exp (r : ℂ)).re = Real.exp r := by
      simpa using Complex.exp_ofReal_re r
    apply UpperHalfPlane.coe_injective
    rw [stabilizerRotation_coe_smul]
    apply (div_eq_iff (denominator_nonzero a b hab (verticalPath r))).2
    apply Complex.ext
    · simp [verticalPath,Complex.add_re,Complex.mul_re,Complex.neg_re,
        Complex.mul_im,Complex.neg_im]
      try rw [hEim]
      dsimp [a,b]
      ring
    · simp [verticalPath,Complex.add_im,Complex.mul_im,Complex.neg_im,
        Complex.mul_re,Complex.neg_re]
      try rw [hEre]
      dsimp [a,b]
      nlinarith [hsphere]
  have exists_stabilizer_radius (r : ℝ) (hr : 0 ≤ r) (z : H2) (h : dist UpperHalfPlane.I z = r) :
      ∃ e : H2 ≃ᵢ H2, e UpperHalfPlane.I = UpperHalfPlane.I ∧ e (verticalPath r) = z := by
    let a : ℝ := 1-Real.exp r*z.im
    let b : ℝ := z.re
    by_cases hpole : a = 0 ∧ b = 0
    · have him : z.im = Real.exp (-r) := by
        have he : Real.exp r ≠ 0 := (Real.exp_pos r).ne'
        have ha : Real.exp r * z.im = 1 := by dsimp [a] at hpole;linarith [hpole.1]
        rw [Real.exp_neg,←one_div]
        exact (eq_div_iff he).2 (by simpa [mul_comm] using ha)
      have hz : z = verticalPath (-r) := by
        apply UpperHalfPlane.ext_re_im
        · simpa [verticalPath,b] using hpole.2
        · simpa [verticalPath] using him
      refine ⟨IsometryEquiv.constSMul
        (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) ModularGroup.S),?_,?_⟩
      · rw [←zero_eq_I]
        change (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S • verticalPath 0 : H2) = verticalPath 0
        have hh := modular_S_verticalPath 0
        change (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S • verticalPath 0 : H2) = verticalPath (-0) at hh
        simpa only [neg_zero] using hh
      · rw [hz]
        change (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S • verticalPath r : H2) = verticalPath (-r)
        exact modular_S_verticalPath r
    · have hab : 0 < a^2+b^2 := by
        by_contra hn
        have ha : a = 0 := by nlinarith [sq_nonneg a,sq_nonneg b]
        have hb : b = 0 := by nlinarith [sq_nonneg a,sq_nonneg b]
        exact hpole ⟨ha,hb⟩
      refine ⟨IsometryEquiv.constSMul (stabilizerRotation a b hab),?_,?_⟩
      · exact stabilizerRotation_fixes_I a b hab
      · exact rotation_maps_vertical_radius r hr z h hab
  have ordered_pair_alignment (x y : H2) :
      ∃ e : H2 ≃ᵢ H2, e UpperHalfPlane.I = x ∧ e (verticalPath (dist x y)) = y := by
    let e0 : H2 ≃ᵢ H2 := IsometryEquiv.constSMul x.toSL2R
    have he0 : e0 UpperHalfPlane.I = x := x.toSL2R_smul_I
    let w := e0.symm y
    have hw : dist UpperHalfPlane.I w = dist x y := by
      have hd := e0.isometry.dist_eq UpperHalfPlane.I (e0.symm y)
      rw [e0.apply_symm_apply,he0] at hd
      exact hd.symm
    obtain ⟨s,hs0,hsr⟩ := exists_stabilizer_radius (dist x y) dist_nonneg w hw
    refine ⟨s.trans e0,?_,?_⟩
    · rw [IsometryEquiv.trans_apply,hs0,he0]
    · rw [IsometryEquiv.trans_apply,hsr]
      exact e0.apply_symm_apply y
  have actual_segment (x y : H2) :
      ∃ γ : Path x y, ∀ s t : unitInterval,
        dist (γ s) (γ t) = dist x y * dist (s : ℝ) (t : ℝ) := by
    obtain ⟨e,he0,he1⟩ := ordered_pair_alignment x y
    let γ : Path x y := {
      toFun := fun t => e (verticalPath ((t : ℝ) * dist x y))
      continuous_toFun := e.continuous.comp
        (verticalPath_isometry.continuous.comp (continuous_subtype_val.mul continuous_const))
      source' := by
        change e (verticalPath (0 * dist x y)) = x
        simpa only [zero_mul,zero_eq_I] using he0
      target' := by
        change e (verticalPath (1 * dist x y)) = y
        simpa only [one_mul] using he1 }
    refine ⟨γ,?_⟩
    intro s t
    change dist (e (verticalPath ((s : ℝ)*dist x y)))
      (e (verticalPath ((t : ℝ)*dist x y))) = _
    rw [e.isometry.dist_eq,verticalPath_isometry.dist_eq,Real.dist_eq,Real.dist_eq,
      ←sub_mul,abs_mul,abs_of_nonneg (dist_nonneg (x := x) (y := y)),mul_comm]
  have locally_isometric_homeomorph_nonexpanding (F : H2 ≃ₜ H2)
      (hF : ∀ x : H2, ∃ U : Set H2, IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, ∀ z ∈ U, dist (F y) (F z) = dist y z)
      (x y : H2) : dist (F x) (F y) ≤ dist x y := by
    obtain ⟨γ,hγ⟩ := actual_segment x y
    choose U hU hxU hmetric using hF
    let V : Interval → Set Interval := fun t => γ ⁻¹' U (γ t)
    have hV (t : Interval) : IsOpen (V t) := (hU (γ t)).preimage γ.continuous
    have hcover : Set.univ ⊆ ⋃ t, V t := by
      intro t ht
      exact Set.mem_iUnion.mpr ⟨t,hxU (γ t)⟩
    obtain ⟨t,ht0,htmono,⟨N,hN⟩,hsub⟩ :=
      exists_monotone_Icc_subset_open_cover_unitInterval hV hcover
    have hstep (n : ℕ) : dist (F (γ (t n))) (F (γ (t (n+1)))) =
        dist x y * ((t (n+1) : ℝ) - (t n : ℝ)) := by
      obtain ⟨j,hj⟩ := hsub n
      have hle : t n ≤ t (n+1) := htmono (Nat.le_succ n)
      have hleft := hj (show t n ∈ Set.Icc (t n) (t (n+1)) from ⟨le_rfl,hle⟩)
      have hright := hj (show t (n+1) ∈ Set.Icc (t n) (t (n+1)) from ⟨hle,le_rfl⟩)
      rw [hmetric (γ j) _ hleft _ hright,hγ,Real.dist_eq,
        abs_of_nonpos (sub_nonpos.mpr (show (t n : ℝ) ≤ (t (n+1) : ℝ) from hle))]
      simp only [neg_sub]
    have hbound (n : ℕ) : dist (F (γ (t 0))) (F (γ (t n))) ≤
        dist x y * ((t n : ℝ) - (t 0 : ℝ)) := by
      induction n with
      | zero => simp
      | succ n ih =>
        have htri := dist_triangle (F (γ (t 0))) (F (γ (t n))) (F (γ (t (n+1))))
        have hsn := hstep n
        nlinarith
    have h := hbound N
    rw [ht0,hN N le_rfl] at h
    simpa using h
  have geometricDeck_inverse_locally_isometric (x : H2) :
      ∃ U : Set H2, IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, ∀ z ∈ U,
          dist (geometricDeck.symm y) (geometricDeck.symm z) = dist y z := by
    obtain ⟨U,hU,hxU,hmetric⟩ := geometricDeck_locally_isometric (geometricDeck.symm x)
    refine ⟨geometricDeck.symm ⁻¹' U,hU.preimage geometricDeck.symm.continuous,hxU,?_⟩
    intro y hy z hz
    have h := hmetric _ hy _ hz
    simpa only [geometricDeck.apply_symm_apply] using h.symm
  have geometricDeck_isometry : Isometry geometricDeck := by
    apply Isometry.of_dist_eq
    intro x y
    apply le_antisymm
    · exact locally_isometric_homeomorph_nonexpanding geometricDeck
        geometricDeck_locally_isometric x y
    · have h := locally_isometric_homeomorph_nonexpanding geometricDeck.symm
        geometricDeck_inverse_locally_isometric (geometricDeck x) (geometricDeck y)
      simpa only [geometricDeck.symm_apply_apply] using h
  let geometricDeckIsometry : H2 ≃ᵢ H2 :=
    { geometricDeck.toEquiv with isometry_toFun := geometricDeck_isometry }
  let developedProjection : H2 → A := fun z => (development.symm z).1
  have developedProjection_continuous : Continuous developedProjection :=
    actualCoveringMap.continuous.comp development.symm.continuous
  have developedProjection_locally_isometric (x : H2) :
      ∃ U : Set H2, IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, ∀ z ∈ U,
          dist (developedProjection y) (developedProjection z) = dist y z := by
    obtain ⟨U,hU,hxU,hmetric⟩ := development_metric (development.symm x)
    refine ⟨development.symm ⁻¹' U,hU.preimage development.symm.continuous,hxU,?_⟩
    intro y hy z hz
    change @dist E H.metric.toDist (development.symm y).1.val
      (development.symm z).1.val = dist y z
    rw [hmetric _ hy _ hz,development.apply_symm_apply,development.apply_symm_apply]
  have developedProjection_nonexpanding (x y : H2) :
      dist (developedProjection x) (developedProjection y) ≤ dist x y := by
    obtain ⟨γ,hγ⟩ := actual_segment x y
    choose U hU hxU hmetric using developedProjection_locally_isometric
    let V : Interval → Set Interval := fun t => γ ⁻¹' U (γ t)
    have hV (t : Interval) : IsOpen (V t) := (hU (γ t)).preimage γ.continuous
    have hcover : Set.univ ⊆ ⋃ t, V t := by
      intro t ht
      exact Set.mem_iUnion.mpr ⟨t,hxU (γ t)⟩
    obtain ⟨t,ht0,htmono,⟨N,hN⟩,hsub⟩ :=
      exists_monotone_Icc_subset_open_cover_unitInterval hV hcover
    have hstep (n : ℕ) :
        dist (developedProjection (γ (t n))) (developedProjection (γ (t (n+1)))) =
          dist x y * ((t (n+1) : ℝ) - (t n : ℝ)) := by
      obtain ⟨j,hj⟩ := hsub n
      have hle : t n ≤ t (n+1) := htmono (Nat.le_succ n)
      have hleft := hj (show t n ∈ Set.Icc (t n) (t (n+1)) from ⟨le_rfl,hle⟩)
      have hright := hj (show t (n+1) ∈ Set.Icc (t n) (t (n+1)) from ⟨hle,le_rfl⟩)
      rw [hmetric (γ j) _ hleft _ hright,hγ,Real.dist_eq,
        abs_of_nonpos (sub_nonpos.mpr (show (t n : ℝ) ≤ (t (n+1) : ℝ) from hle))]
      simp only [neg_sub]
    have hbound (n : ℕ) :
        dist (developedProjection (γ (t 0))) (developedProjection (γ (t n))) ≤
          dist x y * ((t n : ℝ) - (t 0 : ℝ)) := by
      induction n with
      | zero => simp
      | succ n ih =>
        have htri := dist_triangle (developedProjection (γ (t 0)))
          (developedProjection (γ (t n))) (developedProjection (γ (t (n+1))))
        have hsn := hstep n
        nlinarith
    have h := hbound N
    rw [ht0,hN N le_rfl] at h
    simpa using h
  obtain ⟨coverRadius,coverRadius_pos,coverRadius_control⟩ := uniform_evenly_covered_radius
  have actual_positive_uniform_deck_displacement (z : H2) :
      coverRadius ≤ dist z (geometricDeck z) := by
    by_contra hle
    have hshort : dist z (geometricDeck z) < coverRadius := lt_of_not_ge hle
    obtain ⟨a,ha⟩ := coverRadius_control (developedProjection z)
    obtain ⟨γ,hγ⟩ := actual_segment z (geometricDeck z)
    let Γ : C(Interval,P) := ⟨development.symm ∘ γ,
      development.symm.continuous.comp γ.continuous⟩
    let T := actualTrivialization a
    letI : DiscreteTopology ((Sigma.fst : P → A) ⁻¹' {a}) :=
      (actualCoveringMap a).discreteTopology_fiber
    have hsource (t : Interval) : Γ t ∈ T.source := by
      apply T.mem_source.mpr
      apply ha
      change dist (developedProjection (γ t)) (developedProjection z) < coverRadius
      have hπ := developedProjection_nonexpanding (γ t) z
      have hseg : dist (γ t) z = dist z (geometricDeck z) * (t : ℝ) := by
        have h := hγ 0 t
        simpa [Real.dist_eq,abs_of_nonneg t.property.1,dist_comm] using h
      have hbound := mul_le_of_le_one_right
        (dist_nonneg (x := z) (y := geometricDeck z)) t.property.2
      rw [hseg] at hπ
      exact lt_of_le_of_lt (hπ.trans hbound) hshort
    let label : Interval → ((Sigma.fst : P → A) ⁻¹' {a}) := fun t => (T (Γ t)).2
    have hlabel : Continuous label := continuous_snd.comp
      (T.toOpenPartialHomeomorph.continuousOn.comp_continuous Γ.continuous hsource)
    have hlabels : label 0 = label 1 :=
      (isPreconnected_range hlabel).subsingleton (mem_range_self 0) (mem_range_self 1)
    have hprojection : (Γ 0).1 = (Γ 1).1 := by
      change (development.symm (γ 0)).1 = (development.symm (γ 1)).1
      rw [γ.source,γ.target]
      change (development.symm z).1 =
        (development.symm (development (deckTranslation • development.symm z))).1
      rw [development.symm_apply_apply]
      exact (hqc.map_smul deckTranslation).symm
    have hcoords : T (Γ 0) = T (Γ 1) := by
      apply Prod.ext
      · change (T.toOpenPartialHomeomorph (Γ 0)).1 =
          (T.toOpenPartialHomeomorph (Γ 1)).1
        rw [T.proj_toFun _ (hsource 0),T.proj_toFun _ (hsource 1)]
        exact hprojection
      · exact hlabels
    have hend : Γ 0 = Γ 1 := T.injOn (hsource 0) (hsource 1) hcoords
    apply geometricDeck_no_fixed_point z
    have h := congrArg development hend
    change development (development.symm (γ 0)) = development (development.symm (γ 1)) at h
    simpa only [development.apply_symm_apply,γ.source,γ.target] using h.symm
  have developedProjection_deck_invariant (z : H2) :
      developedProjection (geometricDeck z) = developedProjection z := by
    change (development.symm (development
      (deckTranslation • development.symm z))).1 = (development.symm z).1
    rw [development.symm_apply_apply]
    exact hqc.map_smul deckTranslation
  have actual_axis_projects_to_closed_geodesic
      (axis : ℝ → H2) (haxis : Isometry axis) (period : ℝ) (hperiod : 0 < period)
      (htranslation : ∀ t : ℝ, geometricDeck (axis t) = axis (t + period)) :
      @IsClosedGeodesic E (inferInstance : TopologicalSpace E) H.metric
        (Set.range (fun t : ℝ => (developedProjection (axis t)).val)) := by
    let path : ℝ → E := fun t => (developedProjection (axis t)).val
    have hpath : Continuous path := continuous_subtype_val.comp
      (developedProjection_continuous.comp haxis.continuous)
    refine ⟨path,period,hperiod,?_,?_,rfl,?_⟩
    · exact hpath
    · intro t
      change (developedProjection (axis (t + period))).val =
        (developedProjection (axis t)).val
      rw [← htranslation t,developedProjection_deck_invariant]
    · intro t
      obtain ⟨U,hU,htU,hmetric⟩ := developedProjection_locally_isometric (axis t)
      have hopen : IsOpen (axis ⁻¹' U) := hU.preimage haxis.continuous
      obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hopen t htU
      refine ⟨ε,hε,?_⟩
      intro s u hs hu
      have hsU : axis s ∈ U := hball (by simpa only [Metric.mem_ball,Real.dist_eq] using hs)
      have huU : axis u ∈ U := hball (by simpa only [Metric.mem_ball,Real.dist_eq] using hu)
      change dist (developedProjection (axis s)) (developedProjection (axis u)) = |s - u|
      rw [hmetric _ hsU _ huU,haxis.dist_eq,Real.dist_eq]
  have actual_axis_has_circle_geodesic
      (axis : ℝ → H2) (haxis : Isometry axis) (period : ℝ) (hperiod : 0 < period)
      (htranslation : ∀ t : ℝ, geometricDeck (axis t) = axis (t + period)) :
      ∃ g : C(Circle,E),
        @IsParametrizedClosedGeodesic E (inferInstance : TopologicalSpace E) H.metric g ∧
        @IsClosedGeodesic E (inferInstance : TopologicalSpace E) H.metric (Set.range g) ∧
        Set.range g = Set.range (fun t : ℝ => (developedProjection (axis t)).val) ∧
        ∀ t : ℝ, g (circleCoordinate (t : AddCircle (1 : ℝ))) =
          (developedProjection (axis (t * period))).val := by
    let path : ℝ → E := fun t => (developedProjection (axis t)).val
    have hpath : Continuous path := continuous_subtype_val.comp
      (developedProjection_continuous.comp haxis.continuous)
    have hpath_periodic : Function.Periodic path period := by
      intro t
      change (developedProjection (axis (t + period))).val =
        (developedProjection (axis t)).val
      rw [← htranslation t,developedProjection_deck_invariant]
    let descended : C(AddCircle period,E) :=
      ⟨hpath_periodic.lift,continuous_coinduced_dom.mpr hpath⟩
    let coordinate : AddCircle period ≃ₜ Circle := AddCircle.homeomorphCircle hperiod.ne'
    let g : C(Circle,E) := descended.comp ⟨coordinate.symm,coordinate.symm.continuous⟩
    have hrange : Set.range g = Set.range path := by
      apply Set.Subset.antisymm
      · rintro _ ⟨z,rfl⟩
        obtain ⟨t,ht⟩ := QuotientAddGroup.mk_surjective (coordinate.symm z)
        refine ⟨t,?_⟩
        change path t = hpath_periodic.lift (coordinate.symm z)
        rw [← ht]
        rfl
      · rintro _ ⟨t,rfl⟩
        refine ⟨coordinate (t : AddCircle period),?_⟩
        change hpath_periodic.lift (coordinate.symm (coordinate (t : AddCircle period))) = path t
        rw [coordinate.symm_apply_apply]
        rfl
    have hcoordinate (t : ℝ) : coordinate (t : AddCircle period) =
        Circle.exp (2 * Real.pi * t / period) := by
      change AddCircle.homeomorphCircle hperiod.ne' (t : AddCircle period) = _
      rw [AddCircle.homeomorphCircle_apply,AddCircle.toCircle_apply_mk]
      congr 1
      ring
    have hcoordinate_scaled (t : ℝ) :
        coordinate ((t * period : ℝ) : AddCircle period) =
          circleCoordinate (t : AddCircle (1 : ℝ)) := by
      rw [hcoordinate]
      change Circle.exp (2 * Real.pi * (t * period) / period) =
        AddCircle.homeomorphCircle one_ne_zero (t : AddCircle (1 : ℝ))
      rw [AddCircle.homeomorphCircle_apply,AddCircle.toCircle_apply_mk]
      congr 1
      field_simp [hperiod.ne']
    have hunit (t : ℝ) : ∃ ε : ℝ, 0 < ε ∧
        ∀ s u : ℝ, |s-t| < ε → |u-t| < ε →
          @dist E H.metric.toDist (path s) (path u) = |s-u| := by
      obtain ⟨U,hU,htU,hmetric⟩ := developedProjection_locally_isometric (axis t)
      have hopen : IsOpen (axis ⁻¹' U) := hU.preimage haxis.continuous
      obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hopen t htU
      refine ⟨ε,hε,?_⟩
      intro s u hs hu
      have hsU : axis s ∈ U := hball (by simpa only [Metric.mem_ball,Real.dist_eq] using hs)
      have huU : axis u ∈ U := hball (by simpa only [Metric.mem_ball,Real.dist_eq] using hu)
      change dist (developedProjection (axis s)) (developedProjection (axis u)) = |s-u|
      rw [hmetric _ hsU _ huU,haxis.dist_eq,Real.dist_eq]
    refine ⟨g,⟨path,period,Homeomorph.refl Circle,hperiod,hpath,hpath_periodic,?_,hunit⟩,
      ?_,hrange,?_⟩
    · intro t
      change path t = hpath_periodic.lift
        (coordinate.symm (Circle.exp (2 * Real.pi * t / period)))
      rw [← hcoordinate t,coordinate.symm_apply_apply]
      rfl
    · rw [hrange]
      exact actual_axis_projects_to_closed_geodesic axis haxis period hperiod htranslation
    · intro t
      change hpath_periodic.lift (coordinate.symm
        (circleCoordinate (t : AddCircle (1 : ℝ)))) = path (t * period)
      rw [← hcoordinate_scaled t,coordinate.symm_apply_apply]
      rfl
  have actual_hyperbolic_rectangle (bottom top left right : C(Interval,H2))
      (hleft0 : left 0 = bottom 0) (hleft1 : left 1 = top 0)
      (hright0 : right 0 = bottom 1) (hright1 : right 1 = top 1) :
      ∃ H : C(Interval × Interval,H2),
        (∀ t, H (t,0) = bottom t) ∧ (∀ t, H (t,1) = top t) ∧
        (∀ s, H (0,s) = left s) ∧ (∀ s, H (1,s) = right s) := by
    have coezero : ((0 : Interval) : ℝ) = 0 := rfl
    have coeone : ((1 : Interval) : ℝ) = 1 := rfl
    let F : Interval × Interval → ℂ := fun ts =>
      (1 - ts.1.val) • (left ts.2 : ℂ) + ts.1.val • (right ts.2 : ℂ) +
      (1 - ts.2.val) • (bottom ts.1 : ℂ) + ts.2.val • (top ts.1 : ℂ) -
      (1 - ts.2.val) • ((1 - ts.1.val) • (bottom 0 : ℂ) + ts.1.val • (bottom 1 : ℂ)) -
      ts.2.val • ((1 - ts.1.val) • (top 0 : ℂ) + ts.1.val • (top 1 : ℂ))
    have hFleft (s : Interval) : F (0,s) = (left s : ℂ) := by
      dsimp [F]
      simp only [coezero,sub_zero,one_smul,zero_smul,add_zero,zero_add]
      simp only [Complex.real_smul,Complex.ofReal_zero,Complex.ofReal_one,zero_mul,one_mul,mul_zero,mul_one]
      ring
    have hFright (s : Interval) : F (1,s) = (right s : ℂ) := by
      dsimp [F]
      simp only [coeone,sub_self,one_smul,zero_smul,add_zero,zero_add]
      simp only [Complex.real_smul,Complex.ofReal_zero,Complex.ofReal_one,zero_mul,one_mul,mul_zero,mul_one]
      ring
    have hFbottom (t : Interval) : F (t,0) = (bottom t : ℂ) := by
      dsimp [F]
      simp only [coezero,sub_zero,one_smul,zero_smul,add_zero,sub_zero,
        hleft0,hright0]
      simp only [Complex.real_smul,Complex.ofReal_zero,Complex.ofReal_one,zero_mul,one_mul,mul_zero,mul_one]
      ring
    have hFtop (t : Interval) : F (t,1) = (top t : ℂ) := by
      dsimp [F]
      simp only [coeone,sub_self,one_smul,zero_smul,add_zero,zero_add,
        hleft1,hright1]
      simp only [Complex.real_smul,Complex.ofReal_zero,Complex.ofReal_one,zero_mul,one_mul,mul_zero,mul_one]
      ring
    let B : Interval × Interval → ℝ := fun ts =>
      ts.1.val * (1 - ts.1.val) * ts.2.val * (1 - ts.2.val)
    have hpositive (ts : Interval × Interval) : 0 < max (F ts).im (B ts) := by
      obtain ⟨t,s⟩ := ts
      by_cases ht0 : t = 0
      · subst t
        rw [hFleft]
        exact lt_of_lt_of_le (left s).im_pos (le_max_left _ _)
      by_cases ht1 : t = 1
      · subst t
        rw [hFright]
        exact lt_of_lt_of_le (right s).im_pos (le_max_left _ _)
      by_cases hs0 : s = 0
      · subst s
        rw [hFbottom]
        exact lt_of_lt_of_le (bottom t).im_pos (le_max_left _ _)
      by_cases hs1 : s = 1
      · subst s
        rw [hFtop]
        exact lt_of_lt_of_le (top t).im_pos (le_max_left _ _)
      have ht0' : t.val ≠ 0 := fun h => ht0 (Subtype.ext h)
      have ht1' : t.val ≠ 1 := fun h => ht1 (Subtype.ext h)
      have hs0' : s.val ≠ 0 := fun h => hs0 (Subtype.ext h)
      have hs1' : s.val ≠ 1 := fun h => hs1 (Subtype.ext h)
      have ht : 0 < t.val ∧ t.val < 1 :=
        ⟨lt_of_le_of_ne t.property.1 ht0'.symm,lt_of_le_of_ne t.property.2 ht1'⟩
      have hs : 0 < s.val ∧ s.val < 1 :=
        ⟨lt_of_le_of_ne s.property.1 hs0'.symm,lt_of_le_of_ne s.property.2 hs1'⟩
      have hB : 0 < B (t,s) :=
        mul_pos (mul_pos (mul_pos ht.1 (sub_pos.mpr ht.2)) hs.1) (sub_pos.mpr hs.2)
      exact lt_of_lt_of_le hB (le_max_right _ _)
    let H : C(Interval × Interval,H2) := {
      toFun := fun ts => ⟨((F ts).re : ℂ) + ((max (F ts).im (B ts) : ℝ) : ℂ) * Complex.I,
        by simpa using hpositive ts⟩
      continuous_toFun := UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr (by
        change Continuous (fun ts : Interval × Interval =>
          ((F ts).re : ℂ) + ((max (F ts).im (B ts) : ℝ) : ℂ) * Complex.I)
        dsimp [F,B]
        fun_prop) }
    have hboundary (ts : Interval × Interval) (w : H2)
        (hF : F ts = (w : ℂ)) (hB : B ts = 0) : H ts = w := by
      apply UpperHalfPlane.ext
      change ((F ts).re : ℂ) + ((max (F ts).im (B ts) : ℝ) : ℂ) * Complex.I = (w : ℂ)
      rw [hF,hB]
      change (w.re : ℂ) + ((max w.im 0 : ℝ) : ℂ) * Complex.I = (w : ℂ)
      rw [max_eq_left w.im_pos.le]
      exact Complex.re_add_im (w : ℂ)
    refine ⟨H,?_,?_,?_,?_⟩
    · intro t
      exact hboundary (t,0) (bottom t) (hFbottom t) (by simp [B])
    · intro t
      exact hboundary (t,1) (top t) (hFtop t) (by simp [B])
    · intro s
      exact hboundary (0,s) (left s) (hFleft s) (by simp [B])
    · intro s
      exact hboundary (1,s) (right s) (hFright s) (by simp [B])
  have actual_circle_square_descends {E : Type} [TopologicalSpace E] (f g : C(Circle,E))
      (K : C(Interval × Interval,E))
      (hends : ∀ s : Interval, K (0,s) = K (1,s))
      (hbottom : ∀ t : Interval, K (t,0) =
        f (AddCircle.homeomorphCircle one_ne_zero (t.val : AddCircle (1 : ℝ))))
      (htop : ∀ t : Interval, K (t,1) =
        g (AddCircle.homeomorphCircle one_ne_zero (t.val : AddCircle (1 : ℝ)))) :
      ∃ H : C(Circle × Interval,E),
        (∀ z, H (z,0) = f z) ∧ (∀ z, H (z,1) = g z) := by
    let coordinate : AddCircle (1 : ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle one_ne_zero
    let family : C(ℝ,C(Interval,E)) := K.curry.comp
      ⟨Set.projIcc 0 1 zero_le_one,(LipschitzWith.projIcc zero_le_one).continuous⟩
    have hfamily : family 0 = family 1 := by
      apply ContinuousMap.ext
      intro s
      simpa [family] using hends s
    let lifted : C(AddCircle (1 : ℝ),C(Interval,E)) :=
      ⟨AddCircle.liftIco 1 0 family,
        AddCircle.liftIco_zero_continuous hfamily family.continuous.continuousOn⟩
    let H : C(Circle × Interval,E) :=
      (lifted.comp ⟨coordinate.symm,coordinate.symm.continuous⟩).uncurry
    have heval (z : Circle) (s : Interval) :
        H (z,s) = K (Set.projIcc 0 1 zero_le_one
          ((AddCircle.equivIco 1 0) (coordinate.symm z)),s) := by
      rfl
    refine ⟨H,?_,?_⟩
    · intro z
      rw [heval,hbottom]
      let r := (AddCircle.equivIco 1 0) (coordinate.symm z)
      have hr : (r : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨r.property.1,by simpa using r.property.2.le⟩
      rw [Set.projIcc_of_mem zero_le_one hr]
      change f (coordinate ((r : ℝ) : AddCircle (1 : ℝ))) = f z
      rw [AddCircle.coe_equivIco,coordinate.apply_symm_apply]
    · intro z
      rw [heval,htop]
      let r := (AddCircle.equivIco 1 0) (coordinate.symm z)
      have hr : (r : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨r.property.1,by simpa using r.property.2.le⟩
      rw [Set.projIcc_of_mem zero_le_one hr]
      change g (coordinate ((r : ℝ) : AddCircle (1 : ℝ))) = g z
      rw [AddCircle.coe_equivIco,coordinate.apply_symm_apply]
  obtain ⟨actualAxis,actualAxis_isometry,actualPeriod,actualPeriod_pos,actualAxis_translation⟩ :=
    actual_hyperbolic_isometry_axis_of_uniform_displacement geometricDeckIsometry
      coverRadius coverRadius_pos actual_positive_uniform_deck_displacement
  have actualAxis_translation_homeomorph (t : ℝ) :
      geometricDeck (actualAxis t) = actualAxis (t + actualPeriod) :=
    actualAxis_translation t
  obtain ⟨geodesicRepresentative,geodesicRepresentative_parametrized,
      geodesicRepresentative_image,geodesicRepresentative_range,geodesicRepresentative_clock⟩ :=
    actual_axis_has_circle_geodesic actualAxis actualAxis_isometry actualPeriod
      actualPeriod_pos actualAxis_translation_homeomorph
  let bottom : C(Interval,H2) :=
    ⟨fun t => development (liftedPeriodicLoop t.val),development.continuous.comp
      (liftedPeriodicLoop.continuous.comp continuous_subtype_val)⟩
  let top : C(Interval,H2) :=
    ⟨fun t => actualAxis (t.val * actualPeriod),actualAxis_isometry.continuous.comp
      (continuous_subtype_val.mul continuous_const)⟩
  obtain ⟨leftPath,leftPath_metric⟩ := actual_segment (bottom 0) (top 0)
  let left : C(Interval,H2) := ⟨leftPath,leftPath.continuous⟩
  let right : C(Interval,H2) :=
    ⟨fun s => geometricDeck (left s),geometricDeck.continuous.comp left.continuous⟩
  have bottom_deck : geometricDeck (bottom 0) = bottom 1 := by
    change development (deckTranslation.val
      (development.symm (development (liftedPeriodicLoop 0)))) =
      development (liftedPeriodicLoop 1)
    rw [development.symm_apply_apply]
    simpa only [Subgroup.smul_def,Homeomorph.smul_def] using
      congrArg development hdeckTranslation
  have top_deck : geometricDeck (top 0) = top 1 := by
    simpa [top] using actualAxis_translation_homeomorph 0
  obtain ⟨square,square_bottom,square_top,square_left,square_right⟩ :=
    actual_hyperbolic_rectangle bottom top left right leftPath.source leftPath.target
      (by change geometricDeck (leftPath 0) = bottom 1; rw [leftPath.source]; exact bottom_deck)
      (by change geometricDeck (leftPath 1) = top 1; rw [leftPath.target]; exact top_deck)
  let sourceProjection : C(H2,E) :=
    ⟨fun z => (developedProjection z).val,
      continuous_subtype_val.comp developedProjection_continuous⟩
  let sourceSquare : C(Interval × Interval,E) := sourceProjection.comp square
  have sourceSquare_ends (s : Interval) : sourceSquare (0,s) = sourceSquare (1,s) := by
    change (developedProjection (square (0,s))).val =
      (developedProjection (square (1,s))).val
    rw [square_left,square_right]
    change (developedProjection (left s)).val =
      (developedProjection (geometricDeck (left s))).val
    rw [developedProjection_deck_invariant]
  have sourceSquare_bottom (t : Interval) : sourceSquare (t,0) =
      f (AddCircle.homeomorphCircle one_ne_zero (t.val : AddCircle (1 : ℝ))) := by
    change (developedProjection (square (t,0))).val = _
    rw [square_bottom]
    change (development.symm (development (liftedPeriodicLoop t.val))).1.val = _
    rw [development.symm_apply_apply,liftedPeriodicLoop_projection]
    rfl
  have sourceSquare_top (t : Interval) : sourceSquare (t,1) =
      geodesicRepresentative
        (AddCircle.homeomorphCircle one_ne_zero (t.val : AddCircle (1 : ℝ))) := by
    change (developedProjection (square (t,1))).val = _
    rw [square_top]
    change (developedProjection (actualAxis (t.val * actualPeriod))).val =
      geodesicRepresentative (circleCoordinate (t.val : AddCircle (1 : ℝ)))
    exact (geodesicRepresentative_clock t.val).symm
  have geodesicRepresentative_free : FreeHomotopic f geodesicRepresentative :=
    actual_circle_square_descends f geodesicRepresentative sourceSquare sourceSquare_ends
      sourceSquare_bottom sourceSquare_top
  refine ⟨geodesicRepresentative,geodesicRepresentative_free,
    geodesicRepresentative_parametrized,?_,?_⟩
  · intro hf
    have actual_periodic_lift_axis_distance (δ : H2 ≃ᵢ H2) (Γ : C(ℝ,H2)) (a : ℝ → H2) (ha : Isometry a)
        (p : ℝ) (hΓ : ∀ t, Γ (t+1) = δ (Γ t))
        (haxis : ∀ t, δ (a t) = a (t+p)) :
        ∃ B : ℝ, ∀ t : ℝ, dist (Γ t) (a (t*p)) ≤ B := by
      let error (t : ℝ) := dist (Γ t) (a (t*p))
      have hcontinuous : Continuous error :=
        Γ.continuous.dist (ha.continuous.comp (continuous_id.mul continuous_const))
      have hperiod : Function.Periodic error 1 := by
        intro t
        dsimp [error]
        rw [hΓ]
        have htime : (t+1)*p = t*p+p := by ring
        rw [htime,← haxis]
        exact δ.isometry.dist_eq _ _
      obtain ⟨B,hB⟩ := (hperiod.isBounded_of_continuous one_ne_zero hcontinuous).bddAbove
      exact ⟨B, fun t => hB (Set.mem_range_self t)⟩

    have actual_periodic_lift_isProperMap (δ : H2 ≃ᵢ H2) (Γ : C(ℝ,H2)) (a : ℝ → H2) (ha : Isometry a)
        (p : ℝ) (hp : 0 < p) (hΓ : ∀ t, Γ (t+1) = δ (Γ t))
        (haxis : ∀ t, δ (a t) = a (t+p)) : IsProperMap Γ := by
      obtain ⟨B,hB⟩ := actual_periodic_lift_axis_distance δ Γ a ha p hΓ haxis
      refine isProperMap_iff_isCompact_preimage.mpr ⟨Γ.continuous,?_⟩
      intro K hK
      obtain ⟨R,hR⟩ := (hK.image (continuous_id.dist (continuous_const : Continuous (fun _ : H2 => Γ 0)))).bddAbove
      let C := (R+2*B)/p
      have hsubset : Γ ⁻¹' K ⊆ Set.Icc (-C) C := by
        intro t ht
        have htR : dist (Γ t) (Γ 0) ≤ R := hR ⟨Γ t,ht,rfl⟩
        have hd : dist (a (t*p)) (a 0) ≤ B+(R+B) := by
          calc
            dist (a (t*p)) (a 0) ≤ dist (a (t*p)) (Γ t)+dist (Γ t) (a 0) := dist_triangle _ _ _
            _ ≤ B+(dist (Γ t) (Γ 0)+dist (Γ 0) (a 0)) :=
              add_le_add (by simpa only [dist_comm] using hB t) (dist_triangle _ _ _)
            _ ≤ B+(R+B) := by
              have hzero : dist (Γ 0) (a 0) ≤ B := by simpa using hB 0
              linarith
        rw [ha.dist_eq,Real.dist_eq,sub_zero,abs_mul,abs_of_pos hp] at hd
        have habs : |t| ≤ C := (le_div_iff₀ hp).mpr (by linarith)
        exact abs_le.mp habs
      exact isCompact_Icc.of_isClosed_subset (hK.isClosed.preimage Γ.continuous) hsubset
    have actual_proper_embedded_loop_lift_injective {P E : Type} [TopologicalSpace P] [TopologicalSpace E]
        (q : P → E) (hq : IsCoveringMap q) (f : C(Circle,E)) (hf : IsEmbedding f)
        (coordinate : AddCircle (1 : ℝ) ≃ₜ Circle) (Γ : C(ℝ,P)) (hproper : IsProperMap Γ)
        (hprojection : ∀ t : ℝ, q (Γ t) = f (coordinate (t : AddCircle (1 : ℝ)))) :
        Function.Injective Γ := by
      intro x y hxy
      by_contra hne
      have hcircle : (x : AddCircle (1 : ℝ)) = (y : AddCircle (1 : ℝ)) := by
        apply coordinate.injective
        apply hf.injective
        rw [← hprojection,← hprojection,hxy]
      have heq : (fun t : ℝ => Γ (t+x)) = (fun t : ℝ => Γ (t+y)) := by
        refine hq.eq_of_comp_eq (Γ.continuous.comp (continuous_id.add continuous_const))
          (Γ.continuous.comp (continuous_id.add continuous_const)) ?_ 0 ?_
        · funext t
          change q (Γ (t+x)) = q (Γ (t+y))
          rw [hprojection,hprojection,AddCircle.coe_add,AddCircle.coe_add,hcircle]
        · simpa only [zero_add] using hxy
      have hperiod : Function.Periodic Γ (y-x) := by
        intro t
        have h := congrFun heq (t-x)
        have htx : t-x+x=t := by ring
        have hty : t-x+y=t+(y-x) := by ring
        rw [htx,hty] at h
        exact h.symm
      have hrange : IsCompact (Set.range Γ) :=
        hperiod.compact_of_continuous (sub_ne_zero.mpr (by intro h; exact hne h.symm)) Γ.continuous
      have hcompact := hproper.isCompact_preimage hrange
      have huniv : Γ ⁻¹' Set.range Γ = Set.univ := by ext t; simp
      rw [huniv] at hcompact
      exact noncompact_univ ℝ hcompact
    let originalDevelopment : C(ℝ,H2) :=
      ⟨fun t => development (liftedPeriodicLoop t),
        development.continuous.comp liftedPeriodicLoop.continuous⟩
    have originalDevelopment_period (t : ℝ) :
        originalDevelopment (t+1) = geometricDeckIsometry (originalDevelopment t) := by
      change development (liftedPeriodicLoop (t+1)) =
        development (deckTranslation.val (development.symm (development (liftedPeriodicLoop t))))
      rw [development.symm_apply_apply,liftedPeriodicLoop_deck_period]
      rfl
    have originalDevelopment_proper : IsProperMap originalDevelopment :=
      actual_periodic_lift_isProperMap geometricDeckIsometry originalDevelopment actualAxis
        actualAxis_isometry actualPeriod actualPeriod_pos originalDevelopment_period actualAxis_translation
    have originalLift_proper : IsProperMap liftedPeriodicLoop :=
      isProperMap_of_comp_of_inj liftedPeriodicLoop.continuous development.continuous
        originalDevelopment_proper development.injective
    have componentLoop_embedding : IsEmbedding componentLoop :=
      IsEmbedding.of_comp componentLoop.continuous continuous_subtype_val hf
    have originalLift_injective : Function.Injective liftedPeriodicLoop :=
      actual_proper_embedded_loop_lift_injective Sigma.fst actualCoveringMap componentLoop
        componentLoop_embedding circleCoordinate liftedPeriodicLoop originalLift_proper
        liftedPeriodicLoop_projection
    have originalDevelopment_injective : Function.Injective originalDevelopment :=
      development.injective.comp originalLift_injective
    have originalDevelopment_closedEmbedding : IsClosedEmbedding originalDevelopment :=
      IsClosedEmbedding.of_continuous_injective_isClosedMap
        originalDevelopment.continuous originalDevelopment_injective originalDevelopment_proper.isClosedMap
    have actual_embedded_loop_deck_dichotomy {P E : Type} [TopologicalSpace P] [TopologicalSpace E]
        (q : P → E) (hq : IsCoveringMap q) (f : C(Circle,E)) (hf : IsEmbedding f)
        (coordinate : AddCircle (1 : ℝ) ≃ₜ Circle) (Γ : C(ℝ,P))
        (hprojection : ∀ t : ℝ, q (Γ t) = f (coordinate (t : AddCircle (1 : ℝ))))
        (η : P ≃ₜ P) (hη : ∀ z : P, q (η z) = q z) :
        Disjoint (Set.range Γ) (η '' Set.range Γ) ∨ Set.range Γ = η '' Set.range Γ := by
      classical
      by_cases hmeet : ∃ x y : ℝ, Γ x = η (Γ y)
      · right
        obtain ⟨x,y,hxy⟩ := hmeet
        have hcircle : (x : AddCircle (1 : ℝ)) = (y : AddCircle (1 : ℝ)) := by
          apply coordinate.injective
          apply hf.injective
          rw [← hprojection,← hprojection,hxy,hη]
        have heq : (fun t : ℝ => Γ (t+x)) = (fun t : ℝ => η (Γ (t+y))) := by
          refine hq.eq_of_comp_eq (Γ.continuous.comp (continuous_id.add continuous_const))
            (η.continuous.comp (Γ.continuous.comp (continuous_id.add continuous_const))) ?_ 0 ?_
          · funext t
            change q (Γ (t+x)) = q (η (Γ (t+y)))
            rw [hη,hprojection,hprojection,AddCircle.coe_add,AddCircle.coe_add,hcircle]
          · simpa only [zero_add] using hxy
        apply Set.Subset.antisymm
        · rintro _ ⟨t,rfl⟩
          refine ⟨Γ (t-x+y),Set.mem_range_self _,?_⟩
          have h := congrFun heq (t-x)
          simpa only [sub_add_cancel] using h.symm
        · rintro _ ⟨_,⟨t,rfl⟩,rfl⟩
          refine ⟨t-y+x,?_⟩
          have h := congrFun heq (t-y)
          simpa only [sub_add_cancel] using h
      · left
        rw [Set.disjoint_left]
        rintro z ⟨x,hx⟩ ⟨_,⟨y,rfl⟩,hy⟩
        exact hmeet ⟨x,y,hx.trans hy.symm⟩
    have originalLift_deck_dichotomy
        (η : deck (Sigma.fst : P → A)) :
        Disjoint (Set.range liftedPeriodicLoop) (η.val '' Set.range liftedPeriodicLoop) ∨
          Set.range liftedPeriodicLoop = η.val '' Set.range liftedPeriodicLoop := by
      exact actual_embedded_loop_deck_dichotomy Sigma.fst actualCoveringMap componentLoop
        componentLoop_embedding circleCoordinate liftedPeriodicLoop liftedPeriodicLoop_projection
        η.val (by intro z; change (η • z).1 = z.1; exact hqc.map_smul η)
    have actual_complete_geodesic_vertical_normalization (a : ℝ → H2) (ha : Isometry a) :
        ∃ A : SL(2,ℝ), ∀ t : ℝ, (A • verticalPath t : H2) = a t := by
      have hd : dist (a 0) (a 1) = 1 := by
        rw [ha.dist_eq,Real.dist_eq]
        norm_num
      obtain ⟨A,hA0,hA1⟩ := axis_exists_ordered_pair_matrix (a 0) (a 1) hd
      let e : H2 ≃ᵢ H2 := IsometryEquiv.constSMul A
      have he0 : e UpperHalfPlane.I = a 0 := hA0
      have he1 : e (verticalPath 1) = a 1 := hA1
      refine ⟨A,?_⟩
      intro t
      let z := e.symm (a t)
      have hv0 : verticalPath 0 = UpperHalfPlane.I := by
        apply UpperHalfPlane.ext_re_im <;> simp [verticalPath]
      have h0 : dist z UpperHalfPlane.I = dist (verticalPath t) UpperHalfPlane.I := by
        have h := e.isometry.dist_eq z UpperHalfPlane.I
        rw [he0,show e z = a t from e.apply_symm_apply _] at h
        rw [← h,ha.dist_eq]
        simpa only [hv0] using (verticalPath_isometry.dist_eq t 0).symm
      have h1 : dist z (verticalPath 1) = dist (verticalPath t) (verticalPath 1) := by
        have h := e.isometry.dist_eq z (verticalPath 1)
        rw [he1,show e z = a t from e.apply_symm_apply _] at h
        rw [← h,ha.dist_eq]
        exact (verticalPath_isometry.dist_eq t 1).symm
      obtain ⟨him,hre⟩ := axis_two_anchor_coordinates z (verticalPath t) h0 h1
      have hz : z = verticalPath t := by
        apply UpperHalfPlane.ext_re_im
        · simp only [verticalPath,UpperHalfPlane.mk_re] at hre ⊢
          nlinarith only [hre]
        · exact him
      change e (verticalPath t) = a t
      rw [← hz]
      exact e.apply_symm_apply _
    have vertical_coordinate_bounds (z : H2) (t B : ℝ) (hB : 0 ≤ B)
        (hd : dist z (verticalPath t) ≤ B) :
        Real.exp (t-B) ≤ z.im ∧
          ‖(z : ℂ)‖ ≤ (Real.sinh B+Real.cosh B)*Real.exp t := by
      have hlog := (UpperHalfPlane.dist_log_im_le z (verticalPath t)).trans hd
      simp only [verticalPath,UpperHalfPlane.mk_im,Real.log_exp,Real.dist_eq] at hlog
      have hlower : t-B ≤ Real.log z.im := by
        have h := (abs_le.mp hlog).1
        linarith
      have him : Real.exp (t-B) ≤ z.im := by
        have h := Real.exp_le_exp.mpr hlower
        simpa only [Real.exp_log z.im_pos] using h
      refine ⟨him,?_⟩
      have hball := UpperHalfPlane.dist_le_iff_dist_coe_center_le.mp hd
      have hcenter : ((verticalPath t).center B : ℂ) =
          ((Real.exp t*Real.cosh B : ℝ) : ℂ)*Complex.I := by
        apply Complex.ext <;> simp [UpperHalfPlane.center,verticalPath,← Complex.ofReal_exp]
      have hnorm : ‖((verticalPath t).center B : ℂ)‖ = Real.exp t*Real.cosh B := by
        rw [hcenter,norm_mul,Complex.norm_real,Complex.norm_I,mul_one,Real.norm_eq_abs]
        exact abs_of_pos (mul_pos (Real.exp_pos _) (Real.cosh_pos _))
      have hball' : dist (z : ℂ) ((verticalPath t).center B : ℂ) ≤ Real.exp t*Real.sinh B := by
        simpa [verticalPath] using hball
      calc
        ‖(z : ℂ)‖ ≤ dist (z : ℂ) ((verticalPath t).center B : ℂ)+‖((verticalPath t).center B : ℂ)‖ :=
          by simpa only [dist_zero_right] using dist_triangle (z : ℂ) ((verticalPath t).center B : ℂ) 0
        _ ≤ Real.exp t*Real.sinh B+Real.exp t*Real.cosh B := add_le_add hball' hnorm.le
        _ = (Real.sinh B+Real.cosh B)*Real.exp t := by ring

    have cayley_endpoint_bounds (z : H2) :
        dist (cayley z : ℂ) 1 ≤ 2/z.im ∧
          dist (cayley z : ℂ) (-1) ≤ 2*‖(z : ℂ)‖ := by
      have hden : (z : ℂ)+Complex.I ≠ 0 := by
        intro h
        have hi := congrArg Complex.im h
        simp only [Complex.add_im,UpperHalfPlane.coe_im,Complex.I_im,Complex.zero_im] at hi
        linarith [z.im_pos]
      have hnorm : z.im+1 ≤ ‖(z : ℂ)+Complex.I‖ := by
        simpa only [Complex.add_im,UpperHalfPlane.coe_im,Complex.I_im] using
          Complex.im_le_norm ((z : ℂ)+Complex.I)
      have hnorm1 : 1 ≤ ‖(z : ℂ)+Complex.I‖ := by linarith [z.im_pos]
      have hminus : (cayley z : ℂ)-1 = (-2*Complex.I)/((z : ℂ)+Complex.I) := by
        change ((z : ℂ)-Complex.I)/((z : ℂ)+Complex.I)-1 = _
        field_simp [hden] <;> ring
      have hplus : (cayley z : ℂ)-(-1) = (2*(z : ℂ))/((z : ℂ)+Complex.I) := by
        change ((z : ℂ)-Complex.I)/((z : ℂ)+Complex.I)-(-1) = _
        field_simp [hden] <;> ring
      constructor
      · rw [dist_eq_norm,hminus,norm_div,norm_mul]
        norm_num
        apply div_le_div_of_nonneg_left (by norm_num) z.im_pos
        linarith
      · rw [dist_eq_norm,hplus,norm_div,norm_mul]
        norm_num
        exact div_le_self (by positivity) hnorm1

    have actual_bounded_vertical_ideal_endpoints (γ : ℝ → H2) (p B : ℝ) (hp : 0 < p) (hB : 0 ≤ B)
        (hbounded : ∀ t : ℝ, dist (γ t) (verticalPath (p*t)) ≤ B) :
        Tendsto (fun t => (cayley (γ t) : ℂ)) atTop (𝓝 1) ∧
          Tendsto (fun t => (cayley (γ t) : ℂ)) atBot (𝓝 (-1)) := by
      have hneg : Tendsto (fun t : ℝ => B-p*t) atTop atBot := by
        apply tendsto_atBot.mpr
        intro a
        filter_upwards [eventually_ge_atTop ((B-a)/p)] with t ht
        have h := (div_le_iff₀ hp).mp ht
        linarith
      have hbot : Tendsto (fun t : ℝ => p*t) atBot atBot := by
        apply tendsto_atBot.mpr
        intro a
        filter_upwards [eventually_le_atBot (a/p)] with t ht
        simpa only [mul_comm] using (le_div_iff₀ hp).mp ht
      constructor
      · apply tendsto_iff_dist_tendsto_zero.mpr
        have hzero : Tendsto (fun t : ℝ => 2*Real.exp (B-p*t)) atTop (𝓝 0) := by
          simpa only [mul_zero,Function.comp_def] using (Real.tendsto_exp_atBot.comp hneg).const_mul 2
        refine squeeze_zero (fun _ => dist_nonneg) (fun t => ?_) hzero
        have hcoord := (vertical_coordinate_bounds (γ t) (p*t) B hB (hbounded t)).1
        have hbound := (cayley_endpoint_bounds (γ t)).1
        have hquot : 2/Real.exp (p*t-B) = 2*Real.exp (B-p*t) := by
          rw [div_eq_mul_inv,← Real.exp_neg]
          congr 2 <;> ring
        rw [← hquot]
        exact hbound.trans (div_le_div_of_nonneg_left (by norm_num) (Real.exp_pos _) hcoord)
      · apply tendsto_iff_dist_tendsto_zero.mpr
        have hzero : Tendsto (fun t : ℝ => 2*(Real.sinh B+Real.cosh B)*Real.exp (p*t)) atBot (𝓝 0) := by
          simpa only [mul_zero,Function.comp_def] using (Real.tendsto_exp_atBot.comp hbot).const_mul (2*(Real.sinh B+Real.cosh B))
        refine squeeze_zero (fun _ => dist_nonneg) (fun t => ?_) hzero
        have hcoord := (vertical_coordinate_bounds (γ t) (p*t) B hB (hbounded t)).2
        have hbound := (cayley_endpoint_bounds (γ t)).2
        have h := mul_le_mul_of_nonneg_left hcoord (by norm_num : (0:ℝ) ≤ 2)
        exact hbound.trans (by simpa only [mul_assoc] using h)
    have actual_two_endpoint_compactification {X : Type} [TopologicalSpace X] [T2Space X]
        (γ : ℝ → X) (hcontinuous : Continuous γ) (hinjective : Function.Injective γ)
        (a b : X) (hab : a ≠ b)
        (hends : ∀ t : ℝ, γ t ≠ a ∧ γ t ≠ b)
        (hbot : Tendsto γ atBot (𝓝 a)) (htop : Tendsto γ atTop (𝓝 b)) :
        ∃ f : C(unitInterval,X), IsEmbedding f ∧ f 0 = a ∧ f 1 = b ∧
          Set.range f = insert a (insert b (Set.range γ)) := by
      let F : EReal → X := EReal.rec a γ b
      have hF : Continuous F := by
        apply continuous_iff_continuousAt.mpr
        intro x
        cases x using EReal.rec with
        | bot =>
          apply continuousAt_iff_punctured_nhds.mpr
          rw [EReal.nhdsWithin_bot,tendsto_map'_iff]
          simpa only [F,EReal.rec_bot,EReal.rec_coe,Function.comp_def] using hbot
        | coe r =>
          change Tendsto F (𝓝 (r : EReal)) (𝓝 (F r))
          rw [EReal.nhds_coe,tendsto_map'_iff]
          have hr : Tendsto γ (𝓝 r) (𝓝 (γ r)) := hcontinuous.continuousAt
          simpa only [F,EReal.rec_coe,Function.comp_def] using hr
        | top =>
          apply continuousAt_iff_punctured_nhds.mpr
          rw [EReal.nhdsWithin_top,tendsto_map'_iff]
          simpa only [F,EReal.rec_top,EReal.rec_coe,Function.comp_def] using htop
      have hFinj : Function.Injective F := by
        intro x y h
        cases x using EReal.rec <;> cases y using EReal.rec
        all_goals simp only [F,EReal.rec_bot,EReal.rec_top,EReal.rec_coe] at h
        · rfl
        · exact False.elim ((hends _).1 h.symm)
        · exact False.elim (hab h)
        · exact False.elim ((hends _).1 h)
        · exact congrArg (fun t : ℝ => (t : EReal)) (hinjective h)
        · exact False.elim ((hends _).2 h)
        · exact False.elim (hab h.symm)
        · exact False.elim ((hends _).2 h.symm)
        · rfl
      let coordinate : EReal ≃o unitInterval :=
        EReal.expOrderIso.trans ENNReal.orderIsoUnitIntervalBirational
      let e := coordinate.toHomeomorph
      have he0 : e.symm 0 = (⊥ : EReal) := by
        change coordinate.symm ⊥ = ⊥
        exact coordinate.symm.map_bot
      have he1 : e.symm 1 = (⊤ : EReal) := by
        change coordinate.symm ⊤ = ⊤
        exact coordinate.symm.map_top
      let f : C(unitInterval,X) := ⟨F ∘ e.symm,hF.comp e.symm.continuous⟩
      have hf : IsEmbedding f :=
        (f.continuous.isClosedEmbedding (hFinj.comp e.symm.injective)).isEmbedding
      refine ⟨f,hf,?_,?_,?_⟩
      · change F (e.symm 0) = a
        rw [he0]
        rfl
      · change F (e.symm 1) = b
        rw [he1]
        rfl
      · apply Set.Subset.antisymm
        · rintro _ ⟨t,rfl⟩
          change F (e.symm t) ∈ insert a (insert b (Set.range γ))
          cases e.symm t using EReal.rec with
          | bot => simp [F]
          | coe r => exact Set.mem_insert_of_mem a (Set.mem_insert_of_mem b ⟨r,rfl⟩)
          | top => simp [F]
        · intro z hz
          rcases hz with rfl | hz
          · exact ⟨e ⊥,by change F (e.symm (e ⊥)) = F ⊥; exact congrArg F (e.symm_apply_apply _)⟩
          · rcases hz with rfl | ⟨r,rfl⟩
            · exact ⟨e ⊤,by change F (e.symm (e ⊤)) = F ⊤; exact congrArg F (e.symm_apply_apply _)⟩
            · exact ⟨e r,by change F (e.symm (e r)) = γ r; exact congrArg F (e.symm_apply_apply _)⟩
    obtain ⟨normalizer,normalizer_axis⟩ :=
      actual_complete_geodesic_vertical_normalization actualAxis actualAxis_isometry
    let normalizingIsometry : H2 ≃ᵢ H2 := IsometryEquiv.constSMul normalizer
    let normalizedOriginal : C(ℝ,H2) :=
      ⟨fun t => normalizingIsometry.symm (originalDevelopment t),
        normalizingIsometry.symm.continuous.comp originalDevelopment.continuous⟩
    obtain ⟨axisBound,axisBound_control⟩ :=
      actual_periodic_lift_axis_distance geometricDeckIsometry originalDevelopment actualAxis
        actualAxis_isometry actualPeriod originalDevelopment_period actualAxis_translation
    have axisBound_nonnegative : 0 ≤ axisBound := dist_nonneg.trans (axisBound_control 0)
    have normalizedOriginal_bound (t : ℝ) :
        dist (normalizedOriginal t) (verticalPath (actualPeriod*t)) ≤ axisBound := by
      have h := normalizingIsometry.isometry.dist_eq (normalizedOriginal t)
        (verticalPath (actualPeriod*t))
      have hc : normalizingIsometry (normalizedOriginal t) = originalDevelopment t :=
        normalizingIsometry.apply_symm_apply _
      rw [hc] at h
      change dist (originalDevelopment t) (normalizer • verticalPath (actualPeriod*t)) = _ at h
      rw [normalizer_axis] at h
      rw [← h]
      simpa only [mul_comm] using axisBound_control t
    obtain ⟨normalizedOriginal_positive_end,normalizedOriginal_negative_end⟩ :=
      actual_bounded_vertical_ideal_endpoints normalizedOriginal actualPeriod axisBound
        actualPeriod_pos axisBound_nonnegative normalizedOriginal_bound
    let diskOriginal : C(ℝ,ℂ) :=
      ⟨fun t => (cayley (normalizedOriginal t) : ℂ),
        continuous_subtype_val.comp (cayley_continuous.comp normalizedOriginal.continuous)⟩
    have diskOriginal_injective : Function.Injective diskOriginal := by
      intro x y h
      have hC : cayley (normalizedOriginal x) = cayley (normalizedOriginal y) := Subtype.ext h
      have hN := cayley_injective hC
      have hD := normalizingIsometry.symm.injective hN
      exact originalDevelopment_injective hD
    have diskOriginal_interior (t : ℝ) : ‖diskOriginal t‖ < 1 := by
      change ‖(cayley (normalizedOriginal t) : ℂ)‖ < 1
      simpa only [cayley,Metric.mem_ball,dist_zero_right] using cayley_mem_ball (normalizedOriginal t)
    have diskOriginal_off_endpoints (t : ℝ) : diskOriginal t ≠ (-1:ℂ) ∧ diskOriginal t ≠ 1 := by
      constructor
      · intro heq
        have ht := diskOriginal_interior t
        rw [heq] at ht
        norm_num at ht
      · intro heq
        have ht := diskOriginal_interior t
        rw [heq] at ht
        norm_num at ht
    obtain ⟨compactifiedOriginal,compactifiedOriginal_embedding,compactifiedOriginal_left,
      compactifiedOriginal_right,compactifiedOriginal_range⟩ :=
      actual_two_endpoint_compactification diskOriginal diskOriginal.continuous
        diskOriginal_injective (-1:ℂ) 1 (by norm_num) diskOriginal_off_endpoints
        normalizedOriginal_negative_end normalizedOriginal_positive_end
    have actual_embedded_interval_isArc (f : C(unitInterval,ℂ)) (hf : IsEmbedding f) :
        IsArcBetween (actualComplexSchoenflies '' Set.range f)
          (actualComplexSchoenflies (f 0)) (actualComplexSchoenflies (f 1)) := by
      let g : ℝ → Plane := fun r => actualComplexSchoenflies (f (Set.projIcc 0 1 zero_le_one r))
      refine ⟨g, ?_, ?_, ?_, ?_, ?_⟩
      · exact (actualComplexSchoenflies.continuous.comp
          (f.continuous.comp continuous_projIcc)).continuousOn
      · intro x hx y hy h
        have he := hf.injective (actualComplexSchoenflies.injective h)
        have hx' : (Set.projIcc 0 1 zero_le_one x : ℝ) = x := by
          simp [Set.projIcc_of_mem zero_le_one hx]
        have hy' : (Set.projIcc 0 1 zero_le_one y : ℝ) = y := by
          simp [Set.projIcc_of_mem zero_le_one hy]
        simpa only [hx',hy'] using congrArg Subtype.val he
      · ext z
        constructor
        · rintro ⟨r,hr,rfl⟩
          exact ⟨f (Set.projIcc 0 1 zero_le_one r), ⟨_,rfl⟩,rfl⟩
        · rintro ⟨_,⟨r,rfl⟩,rfl⟩
          refine ⟨r.val,r.property,?_⟩
          simp [g,Set.projIcc_of_mem zero_le_one r.property]
      · simp [g,Set.projIcc_of_mem zero_le_one (show (0:ℝ) ∈ Icc 0 1 by simp)]
      · simp [g,Set.projIcc_of_mem zero_le_one (show (1:ℝ) ∈ Icc 0 1 by simp)]
    have actual_unit_disk_inside (hJ : IsJordanCurve (Metric.sphere (0 : Plane) 1)) :
        inside (Metric.sphere (0 : Plane) 1) = Metric.ball (0 : Plane) 1 := by
      have hsub : Metric.ball (0 : Plane) 1 ⊆ (Metric.sphere (0 : Plane) 1)ᶜ := by
        intro x hx hs
        exact (ne_of_lt (Metric.mem_ball.mp hx)) (Metric.mem_sphere.mp hs)
      have hfr : frontier (Metric.ball (0 : Plane) 1) ∩ (Metric.sphere (0 : Plane) 1)ᶜ = ∅ := by
        rw [frontier_ball (0 : Plane) (by norm_num : (1 : ℝ) ≠ 0)]
        exact Set.inter_compl_self _
      have hzero : (0 : Plane) ∈ Metric.ball (0 : Plane) 1 := by simp
      have hcomp := Plane.connectedComponentIn_eq_of_frontier_disjoint
        Metric.isOpen_ball (convex_ball (0 : Plane) 1).isPreconnected hsub hfr hzero
      have hinside : (0 : Plane) ∈ inside (Metric.sphere (0 : Plane) 1) := by
        refine ⟨hsub hzero,?_⟩
        rw [hcomp]
        exact Metric.isBounded_ball
      exact ((jordan_curve_theorem hJ).connectedComponentIn_eq_inside hinside).symm.trans hcomp
    have actual_unit_circle_jordan : IsJordanCurve (Metric.sphere (0 : Plane) 1) := by
      let r : C(Circle,Plane) := ⟨fun z => actualComplexSchoenflies (z : ℂ),
        actualComplexSchoenflies.continuous.comp continuous_subtype_val⟩
      have hr : IsEmbedding r :=
        actualComplexSchoenflies.toHomeomorph.isEmbedding.comp IsEmbedding.subtypeVal
      have h := CurveComplex.isJordanCurve_range_of_isEmbedding_circle r hr
      have heq : Set.range r = Metric.sphere (0 : Plane) 1 := by
        ext x
        constructor
        · rintro ⟨z,rfl⟩
          change dist (actualComplexSchoenflies (z:ℂ)) 0 = 1
          rw [dist_zero_right,actualComplexSchoenflies_norm]
          exact Circle.norm_coe z
        · intro hx
          have hnorm : ‖actualComplexSchoenflies.symm x‖ = 1 := by
            rw [← actualComplexSchoenflies_norm,actualComplexSchoenflies.apply_symm_apply]
            simpa only [Metric.mem_sphere,dist_zero_right] using hx
          let z : Circle := ⟨actualComplexSchoenflies.symm x,
            by
              change actualComplexSchoenflies.symm x ∈ Metric.sphere (0:ℂ) 1
              change dist (actualComplexSchoenflies.symm x) 0 = 1
              simpa only [dist_zero_right] using hnorm⟩
          exact ⟨z,actualComplexSchoenflies.apply_symm_apply x⟩
      rwa [heq] at h
    have actual_compactified_boundary (γ : ℝ → ℂ) (hγ : ∀ t, ‖γ t‖ < 1)
        (f : C(unitInterval,ℂ))
        (hf : Set.range f = insert (-1:ℂ) (insert 1 (Set.range γ))) :
        let P := actualComplexSchoenflies '' Set.range f
        let a := actualComplexSchoenflies (-1:ℂ)
        let b := actualComplexSchoenflies (1:ℂ)
        P ∩ Metric.sphere (0:Plane) 1 = {a,b} ∧
        P \ {a,b} ⊆ Metric.ball (0:Plane) 1 := by
      dsimp
      constructor
      · ext z
        constructor
        · rintro ⟨⟨w,hw,rfl⟩,hz⟩
          rw [hf] at hw
          rcases hw with rfl | hw
          · simp
          rcases hw with rfl | ⟨t,rfl⟩
          · simp
          · have he : ‖γ t‖ = 1 := by
              simpa only [Metric.mem_sphere,dist_zero_right,actualComplexSchoenflies_norm] using hz
            exact (ne_of_lt (hγ t) he).elim
        · intro hz
          rcases hz with rfl | hz
          · refine ⟨⟨-1,?_,rfl⟩,?_⟩
            · rw [hf]; simp
            · simp only [Metric.mem_sphere,dist_zero_right,actualComplexSchoenflies_norm]; norm_num
          · have he : z = actualComplexSchoenflies (1:ℂ) := by simpa using hz
            subst z
            refine ⟨⟨1,?_,rfl⟩,?_⟩
            · rw [hf]; simp
            · simp only [Metric.mem_sphere,dist_zero_right,actualComplexSchoenflies_norm]; norm_num
      · rintro z ⟨⟨w,hw,rfl⟩,hoff⟩
        rw [hf] at hw
        rcases hw with rfl | hw
        · exact (hoff (by simp)).elim
        rcases hw with rfl | ⟨t,rfl⟩
        · exact (hoff (by simp)).elim
        · simpa only [Metric.mem_ball,dist_zero_right,actualComplexSchoenflies_norm] using hγ t
    let originalCrosscut : Set Schoenflies.Plane :=
      actualComplexSchoenflies '' Set.range compactifiedOriginal
    let originalLeft : Schoenflies.Plane := actualComplexSchoenflies (-1:ℂ)
    let originalRight : Schoenflies.Plane := actualComplexSchoenflies (1:ℂ)
    have originalCrosscut_arc : Schoenflies.IsArcBetween originalCrosscut originalLeft originalRight := by
      simpa only [compactifiedOriginal_left,compactifiedOriginal_right] using
        actual_embedded_interval_isArc compactifiedOriginal compactifiedOriginal_embedding
    have originalCrosscut_boundary := actual_compactified_boundary diskOriginal
      diskOriginal_interior compactifiedOriginal compactifiedOriginal_range
    have originalCrosscut_inside : originalCrosscut \ {originalLeft,originalRight} ⊆
        Schoenflies.inside (Metric.sphere (0:Schoenflies.Plane) 1) := by
      rw [actual_unit_disk_inside actual_unit_circle_jordan]
      exact originalCrosscut_boundary.2
    have originalLeft_boundary : originalLeft ∈ Metric.sphere (0:Schoenflies.Plane) 1 := by
      simp only [originalLeft,Metric.mem_sphere,dist_zero_right,actualComplexSchoenflies_norm]
      norm_num
    have originalRight_boundary : originalRight ∈ Metric.sphere (0:Schoenflies.Plane) 1 := by
      simp only [originalRight,Metric.mem_sphere,dist_zero_right,actualComplexSchoenflies_norm]
      norm_num
    have originalEndpoints_ne : originalLeft ≠ originalRight := by
      intro h
      have hc := actualComplexSchoenflies.injective h
      norm_num at hc
    obtain ⟨originalBoundaryFirst,originalBoundarySecond,originalBoundaryCutPair⟩ :=
      Schoenflies.exists_isCutPair actual_unit_circle_jordan originalLeft_boundary
        originalRight_boundary originalEndpoints_ne
    have actual_isometric_arc_transport (g : H2 ≃ᵢ H2) (Γ : ℝ → H2)
        (f : C(unitInterval,Metric.closedBall (0:ℂ) 1)) (hf : IsEmbedding f)
        (a b : Metric.closedBall (0:ℂ) 1)
        (hrange : Set.range f = insert a (insert b (Set.range (fun t => cayley (Γ t))))) :
        ∃ e : Metric.closedBall (0:ℂ) 1 ≃ₜ Metric.closedBall (0:ℂ) 1,
        ∃ F : C(unitInterval,ℂ), IsEmbedding F ∧
          Set.range F = insert (e a:ℂ) (insert (e b:ℂ)
            (Set.range (fun t => (cayley (g (Γ t)):ℂ)))) ∧
          (∀ z : Metric.closedBall (0:ℂ) 1, ‖(e z:ℂ)‖ = 1 ↔ ‖(z:ℂ)‖ = 1) := by
      obtain ⟨e,he,hboundary⟩ := actual_h2_isometry_closed_disk_extension g
      let F : C(unitInterval,ℂ) :=
        ⟨fun s => (e (f s):ℂ),continuous_subtype_val.comp (e.continuous.comp f.continuous)⟩
      have hF : IsEmbedding F :=
        IsEmbedding.subtypeVal.comp (e.isEmbedding.comp hf)
      refine ⟨e,F,hF,?_,hboundary⟩
      ext z
      constructor
      · rintro ⟨s,rfl⟩
        have hs : f s ∈ insert a (insert b (Set.range (fun t => cayley (Γ t)))) := by
          rw [← hrange]
          exact Set.mem_range_self s
        rcases hs with hs | hs
        · change (e (f s):ℂ) ∈ _
          rw [hs]
          exact Set.mem_insert _ _
        rcases hs with hs | ⟨t,ht⟩
        · change (e (f s):ℂ) ∈ _
          rw [hs]
          exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
        · apply Set.mem_insert_of_mem
          apply Set.mem_insert_of_mem
          refine ⟨t,?_⟩
          change (cayley (g (Γ t)):ℂ) = (e (f s):ℂ)
          rw [← he]
          change cayley (Γ t) = f s at ht
          rw [ht]
      · intro hz
        rcases hz with hz | hz
        · have ha : a ∈ Set.range f := by rw [hrange]; simp
          obtain ⟨s,hs⟩ := ha
          exact ⟨s,by change (e (f s):ℂ)=z; rw [hs]; exact hz.symm⟩
        rcases hz with hz | ⟨t,ht⟩
        · have hb : b ∈ Set.range f := by rw [hrange]; simp
          obtain ⟨s,hs⟩ := hb
          exact ⟨s,by change (e (f s):ℂ)=z; rw [hs]; exact hz.symm⟩
        · have hΓ : cayley (Γ t) ∈ Set.range f := by rw [hrange]; simp
          obtain ⟨s,hs⟩ := hΓ
          exact ⟨s,by change (e (f s):ℂ)=z; rw [hs,he]; exact ht⟩
    have originalClosedArc_mem (s : unitInterval) :
        compactifiedOriginal s ∈ Metric.closedBall (0:ℂ) 1 := by
      rw [Metric.mem_closedBall,dist_zero_right]
      have hs : compactifiedOriginal s ∈ insert (-1:ℂ) (insert 1 (Set.range diskOriginal)) := by
        rw [← compactifiedOriginal_range]
        exact Set.mem_range_self s
      rcases hs with hs | hs
      · rw [hs]; norm_num
      rcases hs with hs | ⟨t,ht⟩
      · rw [hs]; norm_num
      · rw [← ht]
        exact (diskOriginal_interior t).le
    let originalClosedArc : C(unitInterval,Metric.closedBall (0:ℂ) 1) :=
      ⟨fun s => ⟨compactifiedOriginal s,originalClosedArc_mem s⟩,
        compactifiedOriginal.continuous.subtype_mk _⟩
    have originalClosedArc_embedding : IsEmbedding originalClosedArc :=
      IsEmbedding.of_comp originalClosedArc.continuous continuous_subtype_val
        compactifiedOriginal_embedding
    let originalDiskLeft : Metric.closedBall (0:ℂ) 1 := ⟨-1,by
      rw [Metric.mem_closedBall,dist_zero_right]; norm_num⟩
    let originalDiskRight : Metric.closedBall (0:ℂ) 1 := ⟨1,by
      rw [Metric.mem_closedBall,dist_zero_right]; norm_num⟩
    have originalClosedArc_range : Set.range originalClosedArc =
        insert originalDiskLeft (insert originalDiskRight
          (Set.range (fun t : ℝ => cayley (normalizedOriginal t)))) := by
      ext z
      constructor
      · rintro ⟨s,rfl⟩
        have hs : compactifiedOriginal s ∈ insert (-1:ℂ) (insert 1 (Set.range diskOriginal)) := by
          rw [← compactifiedOriginal_range]
          exact Set.mem_range_self s
        rcases hs with hs | hs
        · exact Set.mem_insert_iff.mpr (Or.inl (Subtype.ext hs))
        rcases hs with hs | ⟨t,ht⟩
        · apply Set.mem_insert_of_mem
          exact Set.mem_insert_iff.mpr (Or.inl (Subtype.ext hs))
        · apply Set.mem_insert_of_mem
          apply Set.mem_insert_of_mem
          exact ⟨t,Subtype.ext ht⟩
      · intro hz
        rcases hz with hz | hz
        · refine ⟨0,?_⟩
          rw [hz]
          exact Subtype.ext compactifiedOriginal_left
        rcases hz with hz | ⟨t,ht⟩
        · refine ⟨1,?_⟩
          rw [hz]
          exact Subtype.ext compactifiedOriginal_right
        · have hΓ : diskOriginal t ∈ Set.range compactifiedOriginal := by
            rw [compactifiedOriginal_range]
            exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_range_self t))
          obtain ⟨s,hs⟩ := hΓ
          refine ⟨s,?_⟩
          rw [← ht]
          exact Subtype.ext hs
    have original_isometric_translated_arc (g : H2 ≃ᵢ H2) :
        ∃ e : Metric.closedBall (0:ℂ) 1 ≃ₜ Metric.closedBall (0:ℂ) 1,
        ∃ F : C(unitInterval,ℂ), IsEmbedding F ∧
          Set.range F = insert (e originalDiskLeft:ℂ) (insert (e originalDiskRight:ℂ)
            (Set.range (fun t : ℝ => (cayley (g (normalizedOriginal t)):ℂ)))) ∧
          (∀ z : Metric.closedBall (0:ℂ) 1, ‖(e z:ℂ)‖ = 1 ↔ ‖(z:ℂ)‖ = 1) :=
      actual_isometric_arc_transport g normalizedOriginal originalClosedArc
        originalClosedArc_embedding originalDiskLeft originalDiskRight originalClosedArc_range
    have actual_upper_semicircle_arc : IsArcBetween
        (actualComplexSchoenflies '' {z : ℂ | ‖z‖ = 1 ∧ 0 ≤ z.im})
        (actualComplexSchoenflies (-1:ℂ)) (actualComplexSchoenflies (1:ℂ)) := by
      let f : C(unitInterval,ℂ) :=
        ⟨fun t => ((2*(t:ℝ)-1:ℝ):ℂ)+Complex.I*(Real.sqrt (1-(2*(t:ℝ)-1)^2):ℂ),by fun_prop⟩
      have hinj : Function.Injective f := by
        intro s t h
        have hr := congrArg Complex.re h
        simp [f] at hr
        apply Subtype.ext
        linarith
      have hf : IsEmbedding f := (f.continuous.isClosedEmbedding hinj).isEmbedding
      have hrange : Set.range f = {z : ℂ | ‖z‖ = 1 ∧ 0 ≤ z.im} := by
        ext z
        constructor
        · rintro ⟨t,rfl⟩
          have hx : 0 ≤ 1-(2*(t:ℝ)-1)^2 := by
            have hm := mul_nonneg t.property.1 (sub_nonneg.mpr t.property.2)
            nlinarith
          have hs := Real.sq_sqrt hx
          have hn : ‖f t‖^2 = 1 := by
            rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
            simp [f]
            nlinarith
          constructor
          · nlinarith [norm_nonneg (f t)]
          · simp [f,Real.sqrt_nonneg]
        · rintro ⟨hn,hi⟩
          have hre : |z.re| ≤ 1 := by simpa only [hn] using Complex.abs_re_le_norm z
          let t : unitInterval := ⟨(z.re+1)/2,by constructor <;> linarith [abs_le.mp hre]⟩
          refine ⟨t,?_⟩
          have hzsq : z.re^2+z.im^2=1 := by
            have hh : Complex.normSq z=1 := by rw [Complex.normSq_eq_norm_sq,hn]; norm_num
            simpa only [Complex.normSq_apply,pow_two] using hh
          have hroot : Real.sqrt (1-z.re^2)=z.im := by
            rw [show 1-z.re^2=z.im^2 by linarith,Real.sqrt_sq_eq_abs,abs_of_nonneg hi]
          apply Complex.ext
          · simp [f,t]
            ring
          · have he : 2*((z.re+1)/2)-1=z.re := by ring
            simpa only [f,ContinuousMap.coe_mk,t,Complex.add_im,Complex.ofReal_im,
              Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,zero_mul,zero_add,
              one_mul,he] using hroot
      have h0 : f 0=(-1:ℂ) := by simp [f]
      have h1 : f 1=(1:ℂ) := by norm_num [f]
      simpa only [hrange,h0,h1] using actual_embedded_interval_isArc f hf
    
    have actual_arc_homeomorph_image (e : Plane ≃ₜ Plane) {A : Set Plane} {a b : Plane}
        (h : IsArcBetween A a b) : IsArcBetween (e '' A) (e a) (e b) := by
      obtain ⟨f,hc,hi,hr,h0,h1⟩ := h
      refine ⟨e ∘ f,e.continuous.comp_continuousOn hc,?_,?_,?_,?_⟩
      · intro x hx y hy he
        exact hi hx hy (e.injective he)
      · rw [Set.image_comp,hr]
      · simpa only [Function.comp_def,h0]
      · simpa only [Function.comp_def,h1]
    have actual_lower_semicircle_arc : IsArcBetween
        (actualComplexSchoenflies '' {z : ℂ | ‖z‖ = 1 ∧ z.im ≤ 0})
        (actualComplexSchoenflies (-1:ℂ)) (actualComplexSchoenflies (1:ℂ)) := by
      let e : Plane ≃ₜ Plane := actualComplexSchoenflies.symm.toHomeomorph.trans
        (Complex.conjCLE.toHomeomorph.trans actualComplexSchoenflies.toHomeomorph)
      have he (z : ℂ) : e (actualComplexSchoenflies z) = actualComplexSchoenflies (star z) := by
        simp [e,Homeomorph.trans_apply,Complex.conjCLE_apply,Complex.star_def]
      have himage : e '' (actualComplexSchoenflies '' {z : ℂ | ‖z‖=1 ∧ 0 ≤ z.im}) =
          actualComplexSchoenflies '' {z : ℂ | ‖z‖=1 ∧ z.im ≤ 0} := by
        ext z
        constructor
        · rintro ⟨_,⟨w,hw,rfl⟩,rfl⟩
          rw [he]
          refine ⟨star w,⟨?_,?_⟩,rfl⟩
          · simpa only [norm_star] using hw.1
          · simpa [Complex.star_def] using neg_nonpos.mpr hw.2
        · rintro ⟨w,hw,rfl⟩
          refine ⟨actualComplexSchoenflies (star w),?_,?_⟩
          · refine ⟨star w,⟨?_,?_⟩,rfl⟩
            · simpa only [norm_star] using hw.1
            · simpa [Complex.star_def] using neg_nonneg.mpr hw.2
          · rw [he,star_star]
      have h := actual_arc_homeomorph_image e actual_upper_semicircle_arc
      rw [himage,he,he] at h
      simpa using h
    have actual_unit_circle_cut_pair : IsCutPair (Metric.sphere (0:Plane) 1)
        (actualComplexSchoenflies (-1:ℂ)) (actualComplexSchoenflies (1:ℂ))
        (actualComplexSchoenflies '' {z : ℂ | ‖z‖=1 ∧ 0 ≤ z.im})
        (actualComplexSchoenflies '' {z : ℂ | ‖z‖=1 ∧ z.im ≤ 0}) := by
      refine ⟨actual_upper_semicircle_arc,actual_lower_semicircle_arc,?_,?_⟩
      · ext z
        constructor
        · rintro (⟨w,hw,rfl⟩ | ⟨w,hw,rfl⟩) <;>
            simpa only [Metric.mem_sphere,dist_zero_right,actualComplexSchoenflies_norm] using hw.1
        · intro hz
          let w := actualComplexSchoenflies.symm z
          have hn : ‖w‖=1 := by
            rw [← actualComplexSchoenflies_norm]
            simpa only [w,actualComplexSchoenflies.apply_symm_apply,Metric.mem_sphere,dist_zero_right] using hz
          rcases le_total 0 w.im with hi | hi
          · exact Or.inl ⟨w,⟨hn,hi⟩,actualComplexSchoenflies.apply_symm_apply z⟩
          · exact Or.inr ⟨w,⟨hn,hi⟩,actualComplexSchoenflies.apply_symm_apply z⟩
      · ext z
        constructor
        · rintro ⟨⟨w,hw,rfl⟩,⟨v,hv,hvw⟩⟩
          have heq := actualComplexSchoenflies.injective hvw
          subst v
          have him : w.im=0 := le_antisymm hv.2 hw.2
          have hsq : w.re^2=1 := by
            have hn : Complex.normSq w=1 := by rw [Complex.normSq_eq_norm_sq,hw.1]; norm_num
            simp only [Complex.normSq_apply,him,mul_zero,add_zero] at hn
            simpa only [pow_two] using hn
          rcases (sq_eq_one_iff.mp hsq) with hr | hr
          · right
            have hw1 : w=(1:ℂ) := by apply Complex.ext <;> simp [hr,him]
            simp [hw1]
          · left
            have hw1 : w=(-1:ℂ) := by apply Complex.ext <;> simp [hr,him]
            simp [hw1]
        · intro hz
          rcases hz with hz | hz
          · rw [hz]
            constructor <;> exact ⟨-1,by simp,rfl⟩
          · have hz1 : z=actualComplexSchoenflies (1:ℂ) := by simpa using hz
            rw [hz1]
            constructor <;> exact ⟨1,by simp,rfl⟩
    let originalUpperBoundary : Set Schoenflies.Plane :=
      actualComplexSchoenflies '' {z : ℂ | ‖z‖=1 ∧ 0 ≤ z.im}
    let originalLowerBoundary : Set Schoenflies.Plane :=
      actualComplexSchoenflies '' {z : ℂ | ‖z‖=1 ∧ z.im ≤ 0}
    have originalActualBoundaryCutPair : IsCutPair (Metric.sphere (0:Plane) 1)
        originalLeft originalRight originalUpperBoundary originalLowerBoundary :=
      actual_unit_circle_cut_pair
    have actual_hemisphere_meeting {P Q : Set Plane} (hC : IsJordanCurve (Metric.sphere (0:Plane) 1))
        (hP : IsArcBetween P (actualComplexSchoenflies (-1:ℂ)) (actualComplexSchoenflies (1:ℂ)))
        (hPC : P ∩ Metric.sphere (0:Plane) 1 =
          {actualComplexSchoenflies (-1:ℂ),actualComplexSchoenflies (1:ℂ)})
        (hPD : P \ {actualComplexSchoenflies (-1:ℂ),actualComplexSchoenflies (1:ℂ)} ⊆
          inside (Metric.sphere (0:Plane) 1))
        (hQ : IsPreconnected Q) (hQD : Q ⊆ inside (Metric.sphere (0:Plane) 1))
        (w₁ w₂ : ℂ) (hn₁ : ‖w₁‖=1) (hn₂ : ‖w₂‖=1)
        (hi₁ : 0 < w₁.im) (hi₂ : w₂.im < 0)
        (hw₁ : actualComplexSchoenflies w₁ ∈ closure Q)
        (hw₂ : actualComplexSchoenflies w₂ ∈ closure Q) : (Q ∩ P).Nonempty := by
      have h₁ : actualComplexSchoenflies w₁ ∈
          actualComplexSchoenflies '' {z : ℂ | ‖z‖=1 ∧ 0 ≤ z.im} := ⟨w₁,⟨hn₁,hi₁.le⟩,rfl⟩
      have h₂ : actualComplexSchoenflies w₂ ∈
          actualComplexSchoenflies '' {z : ℂ | ‖z‖=1 ∧ z.im ≤ 0} := ⟨w₂,⟨hn₂,hi₂.le⟩,rfl⟩
      have h₁not : actualComplexSchoenflies w₁ ∉
          actualComplexSchoenflies '' {z : ℂ | ‖z‖=1 ∧ z.im ≤ 0} := by
        rintro ⟨v,hv,he⟩
        have hvw := actualComplexSchoenflies.injective he
        subst v
        exact (not_le_of_gt hi₁) hv.2
      have h₂not : actualComplexSchoenflies w₂ ∉
          actualComplexSchoenflies '' {z : ℂ | ‖z‖=1 ∧ 0 ≤ z.im} := by
        rintro ⟨v,hv,he⟩
        have hvw := actualComplexSchoenflies.injective he
        subst v
        exact (not_le_of_gt hi₂) hv.2
      exact arbitrary_jordan_crosscut_alternating_inter_nonempty hC hP actual_unit_circle_cut_pair
        hPC hPD hQ hQD hw₁ hw₂ h₁ h₁not h₂ h₂not
    
    have actual_isometric_lift_crossing (Γ : C(ℝ,H2)) (P : Set Plane)
        (hP : IsArcBetween P (actualComplexSchoenflies (-1:ℂ)) (actualComplexSchoenflies (1:ℂ)))
        (hPC : P ∩ Metric.sphere (0:Plane) 1 =
          {actualComplexSchoenflies (-1:ℂ),actualComplexSchoenflies (1:ℂ)})
        (hPD : P \ {actualComplexSchoenflies (-1:ℂ),actualComplexSchoenflies (1:ℂ)} ⊆
          inside (Metric.sphere (0:Plane) 1))
        (hPrange : P=insert (actualComplexSchoenflies (-1:ℂ))
          (insert (actualComplexSchoenflies (1:ℂ))
            (Set.range (fun t : ℝ => actualComplexSchoenflies (cayley (Γ t):ℂ)))))
        (hbot : Tendsto (fun t => (cayley (Γ t):ℂ)) atBot (𝓝 (-1:ℂ)))
        (htop : Tendsto (fun t => (cayley (Γ t):ℂ)) atTop (𝓝 (1:ℂ)))
        (g : H2 ≃ᵢ H2)
        (e : Metric.closedBall (0:ℂ) 1 ≃ₜ Metric.closedBall (0:ℂ) 1)
        (he : ∀ z : H2, e (cayley z)=cayley (g z))
        (hboundary : ∀ z : Metric.closedBall (0:ℂ) 1, ‖(e z:ℂ)‖=1 ↔ ‖(z:ℂ)‖=1)
        (a b : Metric.closedBall (0:ℂ) 1) (ha : (a:ℂ)=(-1:ℂ)) (hb : (b:ℂ)=(1:ℂ))
        (hsign : (e a:ℂ).im*(e b:ℂ).im < 0) :
        ∃ s t : ℝ, Γ s=g (Γ t) := by
      let Q : Set Plane := Set.range (fun t : ℝ => actualComplexSchoenflies (cayley (g (Γ t)):ℂ))
      have hQ : IsPreconnected Q := isPreconnected_range
        (actualComplexSchoenflies.continuous.comp
          (continuous_subtype_val.comp (cayley_continuous.comp (g.continuous.comp Γ.continuous))))
      have hQD : Q ⊆ inside (Metric.sphere (0:Plane) 1) := by
        rw [actual_unit_disk_inside actual_unit_circle_jordan]
        rintro z ⟨t,rfl⟩
        simpa only [Metric.mem_ball,dist_zero_right,actualComplexSchoenflies_norm,cayley] using
          cayley_mem_ball (g (Γ t))
      have hclosure {l : Filter ℝ} [NeBot l] (c : Metric.closedBall (0:ℂ) 1)
          (hl : Tendsto (fun t => (cayley (Γ t):ℂ)) l (𝓝 (c:ℂ))) :
          actualComplexSchoenflies (e c:ℂ) ∈ closure Q := by
        have ht : Tendsto (fun t => cayley (Γ t)) l (𝓝 c) := tendsto_subtype_rng.mpr hl
        have htrans : Tendsto (fun t => actualComplexSchoenflies (e (cayley (Γ t)):ℂ))
            l (𝓝 (actualComplexSchoenflies (e c:ℂ))) :=
          (actualComplexSchoenflies.continuous.continuousAt.tendsto).comp
            ((continuous_subtype_val.continuousAt.tendsto).comp
              (e.continuous.continuousAt.tendsto.comp ht))
        have hactual : Tendsto (fun t : ℝ => actualComplexSchoenflies (cayley (g (Γ t)):ℂ))
            l (𝓝 (actualComplexSchoenflies (e c:ℂ))) := by simpa only [he] using htrans
        exact mem_closure_of_tendsto hactual (Filter.Eventually.of_forall (fun t => Set.mem_range_self t))
      have hca := hclosure a (by simpa only [ha] using hbot)
      have hcb := hclosure b (by simpa only [hb] using htop)
      have hna : ‖(e a:ℂ)‖=1 := (hboundary a).mpr (by rw [ha]; norm_num)
      have hnb : ‖(e b:ℂ)‖=1 := (hboundary b).mpr (by rw [hb]; norm_num)
      have hmeet : (Q ∩ P).Nonempty := by
        rcases mul_neg_iff.mp hsign with hcase | hcase
        · first
          | exact actual_hemisphere_meeting actual_unit_circle_jordan hP hPC hPD hQ hQD
              (e a:ℂ) (e b:ℂ) hna hnb hcase.1 hcase.2 hca hcb
          | exact actual_hemisphere_meeting actual_unit_circle_jordan hP hPC hPD hQ hQD
              (e b:ℂ) (e a:ℂ) hnb hna hcase.2 hcase.1 hcb hca
        · first
          | exact actual_hemisphere_meeting actual_unit_circle_jordan hP hPC hPD hQ hQD
              (e a:ℂ) (e b:ℂ) hna hnb hcase.1 hcase.2 hca hcb
          | exact actual_hemisphere_meeting actual_unit_circle_jordan hP hPC hPD hQ hQD
              (e b:ℂ) (e a:ℂ) hnb hna hcase.2 hcase.1 hcb hca
      obtain ⟨z,hzQ,hzP⟩ := hmeet
      have hznot : z ∉ Metric.sphere (0:Plane) 1 := inside_subset_compl (hQD hzQ)
      obtain ⟨t,ht⟩ := hzQ
      rw [hPrange] at hzP
      rcases hzP with hleft | hzP
      · rw [hleft] at hznot
        exact (hznot (by simp [Metric.mem_sphere,dist_zero_right,actualComplexSchoenflies_norm])).elim
      rcases hzP with hright | ⟨s,hs⟩
      · rw [hright] at hznot
        exact (hznot (by simp [Metric.mem_sphere,dist_zero_right,actualComplexSchoenflies_norm])).elim
      · refine ⟨s,t,?_⟩
        apply cayley_injective
        apply Subtype.ext
        exact actualComplexSchoenflies.injective (hs.trans ht.symm)
    have originalCrosscut_range : originalCrosscut =
        insert (actualComplexSchoenflies (-1:ℂ))
          (insert (actualComplexSchoenflies (1:ℂ))
            (Set.range (fun t : ℝ => actualComplexSchoenflies (cayley (normalizedOriginal t):ℂ)))) := by
      change actualComplexSchoenflies '' Set.range compactifiedOriginal = _
      rw [compactifiedOriginal_range,Set.image_insert_eq,Set.image_insert_eq,← Set.range_comp]
      rfl
    have original_isometric_lift_crossing (g : H2 ≃ᵢ H2)
        (e : Metric.closedBall (0:ℂ) 1 ≃ₜ Metric.closedBall (0:ℂ) 1)
        (he : ∀ z : H2, e (cayley z)=cayley (g z))
        (hboundary : ∀ z : Metric.closedBall (0:ℂ) 1, ‖(e z:ℂ)‖=1 ↔ ‖(z:ℂ)‖=1)
        (hsign : (e originalDiskLeft:ℂ).im*(e originalDiskRight:ℂ).im < 0) :
        ∃ s t : ℝ, normalizedOriginal s=g (normalizedOriginal t) :=
      actual_isometric_lift_crossing normalizedOriginal originalCrosscut originalCrosscut_arc
        originalCrosscut_boundary.1 originalCrosscut_inside originalCrosscut_range
        normalizedOriginal_negative_end normalizedOriginal_positive_end g e he hboundary
        originalDiskLeft originalDiskRight rfl rfl hsign
    have actual_normalized_deck_isometry (η : P ≃ₜ P)
        (hη : ∀ x : P, (η x).1 = x.1) :
        ∃ g : H2 ≃ᵢ H2, ∀ t : ℝ,
          g (normalizedOriginal t) =
            normalizingIsometry.symm (development (η (liftedPeriodicLoop t))) := by
      let g₀ : H2 ≃ᵢ H2 :=
        { ((development.symm.trans η).trans development).toEquiv with
          isometry_toFun := actual_deck_development_isometric η hη }
      let g : H2 ≃ᵢ H2 :=
        (normalizingIsometry.trans g₀).trans normalizingIsometry.symm
      refine ⟨g,?_⟩
      intro t
      change normalizingIsometry.symm
        (development (η (development.symm
          (normalizingIsometry (normalizingIsometry.symm (development (liftedPeriodicLoop t))))))) = _
      rw [normalizingIsometry.apply_symm_apply,development.symm_apply_apply]
    have original_distinct_axis_crossing_meets_lift (g : H2 ≃ᵢ H2) (t : ℝ)
        (hcross : (g (verticalPath t)).re=0)
        (hne : Set.range (fun s : ℝ => g (verticalPath s)) ≠ Set.range verticalPath) :
        ∃ s u : ℝ, normalizedOriginal s=g (normalizedOriginal u) := by
      obtain ⟨e,he,hboundary,hsign⟩ :=
        actual_distinct_isometry_axis_crossing_disk_sign g t hcross hne
          originalDiskLeft originalDiskRight rfl rfl
      exact original_isometric_lift_crossing g e he hboundary hsign
    have original_deck_axis_crossing_preserves_lift
        (η : deck (Sigma.fst : P → A))
        (g : H2 ≃ᵢ H2)
        (hg : ∀ t : ℝ, g (normalizedOriginal t) =
          normalizingIsometry.symm (development (η • liftedPeriodicLoop t)))
        (t : ℝ) (hcross : (g (verticalPath t)).re=0)
        (hne : Set.range (fun s : ℝ => g (verticalPath s)) ≠ Set.range verticalPath) :
        Set.range liftedPeriodicLoop = η.val '' Set.range liftedPeriodicLoop := by
      obtain ⟨s,u,hsu⟩ := original_distinct_axis_crossing_meets_lift g t hcross hne
      have hm : liftedPeriodicLoop s=η • liftedPeriodicLoop u := by
        apply development.injective
        apply normalizingIsometry.symm.injective
        change normalizedOriginal s = normalizingIsometry.symm
          (development (η • liftedPeriodicLoop u))
        exact hsu.trans (hg u)
      rcases originalLift_deck_dichotomy η with hd | he
      · exfalso
        exact (Set.disjoint_left.mp hd) (Set.mem_range_self s)
          ⟨liftedPeriodicLoop u,Set.mem_range_self u,hm.symm⟩
      · exact he
    have original_deck_stabilizer_monodromy
        (η : deck (Sigma.fst : P → A))
        (hstable : η • liftedPeriodicLoop 0 ∈ Set.range liftedPeriodicLoop) :
        ∃ k : ℤ, η=deckTranslation^k := by
      exact actual_embedded_lift_stabilizer_monodromy Sigma.fst hqc componentLoop
        componentLoop_embedding circleCoordinate liftedPeriodicLoop
        liftedPeriodicLoop_projection deckTranslation η liftedPeriodicLoop_deck_period hstable
    have original_distinct_deck_axes_cannot_cross
        (η : deck (Sigma.fst : P → A)) (g : H2 ≃ᵢ H2)
        (hg : ∀ z : H2, g z = normalizingIsometry.symm
          (development (η • development.symm (normalizingIsometry z))))
        (t : ℝ) (hcross : (g (verticalPath t)).re=0)
        (hne : Set.range (fun s : ℝ => g (verticalPath s)) ≠ Set.range verticalPath) : False := by
      have hgΓ (s : ℝ) : g (normalizedOriginal s)=
          normalizingIsometry.symm (development (η • liftedPeriodicLoop s)) := by
        rw [hg]
        change normalizingIsometry.symm (development (η • development.symm
          (normalizingIsometry (normalizingIsometry.symm (development (liftedPeriodicLoop s)))))) = _
        rw [normalizingIsometry.apply_symm_apply,development.symm_apply_apply]
      have he := original_deck_axis_crossing_preserves_lift η g hgΓ t hcross hne
      have hstable : η • liftedPeriodicLoop 0 ∈ Set.range liftedPeriodicLoop := by
        rw [he]
        exact ⟨liftedPeriodicLoop 0,Set.mem_range_self 0,rfl⟩
      obtain ⟨k,hk⟩ := original_deck_stabilizer_monodromy η hstable
      let liftedAxis : ℝ → P := fun s => development.symm (actualAxis s)
      have haxis : ∀ s : ℝ, liftedAxis (s+actualPeriod)=deckTranslation • liftedAxis s := by
        intro s
        apply development.injective
        change development (development.symm (actualAxis (s+actualPeriod)))=
          development (deckTranslation • development.symm (actualAxis s))
        rw [development.apply_symm_apply]
        exact (actualAxis_translation s).symm
      have hpowrange := actual_deck_power_axis_range deckTranslation liftedAxis actualPeriod
        actualPeriod_pos.ne' haxis k
      have hgvertical (s : ℝ) : (g (verticalPath s)).re=0 := by
        have hm : deckTranslation^k • liftedAxis s ∈ Set.range liftedAxis := by
          rw [←hpowrange]
          exact Set.mem_range_self s
        obtain ⟨u,hu⟩ := hm
        have hn (v : ℝ) : normalizingIsometry (verticalPath v)=actualAxis v := normalizer_axis v
        have hcalc : g (verticalPath s)=verticalPath u := by
          rw [hg,hn,hk]
          change normalizingIsometry.symm (development (deckTranslation^k • liftedAxis s))=verticalPath u
          rw [←hu]
          change normalizingIsometry.symm (development (development.symm (actualAxis u)))=verticalPath u
          rw [development.apply_symm_apply,←hn,normalizingIsometry.symm_apply_apply]
        rw [hcalc]
        rfl
      exact hne (vertical_line_range (fun s : ℝ => g (verticalPath s))
        (g.isometry.comp verticalPath_isometry) hgvertical)
    let normalizedDevelopment : P ≃ₜ H2 :=
      development.trans normalizingIsometry.symm.toHomeomorph
    have normalizedDevelopment_metric : ∀x : P, ∃U : Set P, IsOpen U ∧ x∈U ∧
        ∀y∈U, ∀z∈U, dist y.1 z.1=dist (normalizedDevelopment y) (normalizedDevelopment z) := by
      intro x
      obtain ⟨U,hU,hx,hmetric⟩ := development_metric x
      refine ⟨U,hU,hx,?_⟩
      intro y hy z hz
      have hd := normalizingIsometry.symm.isometry.dist_eq (development y) (development z)
      exact (hmetric y hy z hz).trans hd.symm
    have normalized_original_axis_period (s : ℝ) :
        normalizedDevelopment (deckTranslation • normalizedDevelopment.symm (verticalPath s))=
          verticalPath (s+actualPeriod) := by
      change normalizingIsometry.symm (development
        (deckTranslation • development.symm (normalizingIsometry (verticalPath s))))=verticalPath (s+actualPeriod)
      rw [show normalizingIsometry (verticalPath s)=actualAxis s from normalizer_axis s]
      change normalizingIsometry.symm (geometricDeck (actualAxis s))=verticalPath (s+actualPeriod)
      rw [actualAxis_translation_homeomorph,←normalizer_axis]
      exact normalizingIsometry.symm_apply_apply _
    obtain ⟨axisPeriodHom,axisPeriodHom_injective,axisPeriodHom_action,
      minimalAxisPeriod,minimalAxisPeriod_pos,minimalAxisDeck,minimalAxisDeck_period,axisPeriods_lattice⟩ :=
      actual_source_axis_minimal_period Sigma.fst hqc normalizedDevelopment
        normalizedDevelopment_metric deckTranslation actualPeriod actualPeriod_pos
        normalized_original_axis_period
    have actual_normalized_axis_meeting_stabilizes
        (η : deck (Sigma.fst : P → A)) (s u : ℝ)
        (hmeet : η • normalizedDevelopment.symm (verticalPath u)=
          normalizedDevelopment.symm (verticalPath s)) :
        η∈MulAction.stabilizer (deck (Sigma.fst : P → A))
          (Set.range (fun t : ℝ => normalizedDevelopment.symm (verticalPath t))) := by
      let g₀ : H2 ≃ᵢ H2 :=
        { ((development.symm.trans η.val).trans development).toEquiv with
          isometry_toFun := actual_deck_development_isometric η.val
            (fun x => hqc.map_smul η) }
      let g : H2 ≃ᵢ H2 := (normalizingIsometry.trans g₀).trans normalizingIsometry.symm
      have hg (z : H2) : g z=normalizingIsometry.symm
          (development (η • development.symm (normalizingIsometry z))) := rfl
      have heaction (t : ℝ) : g (verticalPath t)=normalizedDevelopment
          (η • normalizedDevelopment.symm (verticalPath t)) := rfl
      have hv : g (verticalPath u)=verticalPath s := by
        rw [heaction,hmeet,normalizedDevelopment.apply_symm_apply]
      have hc : (g (verticalPath u)).re=0 := by rw [hv]; rfl
      have hrange : Set.range (fun t : ℝ => g (verticalPath t))=Set.range verticalPath := by
        by_contra hne
        exact original_distinct_deck_axes_cannot_cross η g hg u hc hne
      apply MulAction.mem_stabilizer_iff.mpr
      change (fun z : P => η • z) ''
        Set.range (fun t : ℝ => normalizedDevelopment.symm (verticalPath t))=
        Set.range (fun t : ℝ => normalizedDevelopment.symm (verticalPath t))
      apply Set.Subset.antisymm
      · rintro _ ⟨_,⟨t,rfl⟩,rfl⟩
        have hm : g (verticalPath t)∈Set.range verticalPath := by
          rw [←hrange]
          exact Set.mem_range_self t
        obtain ⟨v,hv⟩ := hm
        refine ⟨v,?_⟩
        apply normalizedDevelopment.injective
        rw [normalizedDevelopment.apply_symm_apply,←heaction]
        exact hv
      · rintro _ ⟨t,rfl⟩
        have hm : verticalPath t∈Set.range (fun v : ℝ => g (verticalPath v)) := by
          rw [hrange]
          exact Set.mem_range_self t
        obtain ⟨v,hv⟩ := hm
        refine ⟨normalizedDevelopment.symm (verticalPath v),Set.mem_range_self v,?_⟩
        apply normalizedDevelopment.injective
        rw [←heaction,normalizedDevelopment.apply_symm_apply]
        exact hv
    obtain ⟨primitiveCurvePeriod,primitiveCurvePeriod_pos,primitiveAxisCurveA,
      primitiveAxisCurveA_embedding,primitiveAxisCurveA_clock,primitiveAxisMonodromy,
      primitiveAxisMonodromy_action,primitiveAxisPeriods⟩ :=
      actual_source_minimal_axis_curve Sigma.fst hqc normalizedDevelopment
        normalizedDevelopment_metric deckTranslation actualPeriod actualPeriod_pos
        normalized_original_axis_period actual_normalized_axis_meeting_stabilizes
    let primitiveAxisCurve : Curve E :=
      { map := fun z => (primitiveAxisCurveA z).val
        embedded := IsEmbedding.subtypeVal.comp primitiveAxisCurveA_embedding }
    letI : ClosedSurface E := hE.2.1.some
    have primitiveAxisCurve_has_collar :
        ∃ collar : C(Set.Ioo (-1:ℝ) 1 × Circle,E), IsOpenEmbedding collar ∧
          ∀w : Circle, collar (⟨0,by norm_num⟩,w)=primitiveAxisCurve.map w := by
      rcases embedded_circle_annular_collar_or_local_reflection E primitiveAxisCurve with
        hcollar | ⟨x,hreflection⟩
      · exact hcollar
      · exact False.elim (GenusOrientationCandidate.no_local_reflection_witness 2 hE x
          (GenusOrientationCandidate.surface_puncture_homologyInclusion_zero x) hreflection.some)
    obtain ⟨primitiveAxisCollar,primitiveAxisCollar_embedding,primitiveAxisCollar_core⟩ :=
      primitiveAxisCurve_has_collar
    have primitiveAxisCollar_component (wt : Set.Ioo (-1:ℝ) 1 × Circle) :
        primitiveAxisCollar wt ∈ A := by
      change primitiveAxisCollar wt ∈ connectedComponent (f 1)
      rw [PreconnectedSpace.connectedComponent_eq_univ]
      trivial
    let primitiveAxisCollarA : C(Set.Ioo (-1:ℝ) 1 × Circle,A) :=
      ⟨fun wt => ⟨primitiveAxisCollar wt,primitiveAxisCollar_component wt⟩,
        primitiveAxisCollar.continuous.subtype_mk primitiveAxisCollar_component⟩
    have primitiveAxisCollarA_injective : Function.Injective primitiveAxisCollarA := by
      intro x y h
      apply primitiveAxisCollar_embedding.injective
      exact congrArg Subtype.val h
    have primitiveAxisCollarA_clock (t : ℝ) :
        primitiveAxisCollarA (⟨0,by norm_num⟩,
          AddCircle.homeomorphCircle primitiveCurvePeriod_pos.ne' (t:AddCircle primitiveCurvePeriod))=
          (normalizedDevelopment.symm (verticalPath t)).1 := by
      apply Subtype.ext
      change primitiveAxisCollar (⟨0,by norm_num⟩,
          AddCircle.homeomorphCircle primitiveCurvePeriod_pos.ne' (t:AddCircle primitiveCurvePeriod))=
          (normalizedDevelopment.symm (verticalPath t)).1.val
      rw [primitiveAxisCollar_core]
      exact congrArg Subtype.val (primitiveAxisCurveA_clock t)
    have primitive_axis_monodromy_not_glide (scale : ℝ) (hscale : 0 < scale)
        (hflip : ∀z : H2,
          (normalizedDevelopment (primitiveAxisMonodromy • normalizedDevelopment.symm z)).re=
            -scale*z.re) : False := by
      exact actual_lifted_axis_collar_excludes_glide Sigma.fst actualCoveringMap
        normalizedDevelopment primitiveCurvePeriod primitiveCurvePeriod_pos primitiveAxisMonodromy.val
        (fun x => hqc.map_smul primitiveAxisMonodromy) primitiveAxisCollarA
        primitiveAxisCollarA_injective primitiveAxisCollarA_clock
        primitiveAxisMonodromy_action scale hscale hflip
    let primitiveGeometricDeck : H2 ≃ᵢ H2 :=
      { ((normalizedDevelopment.symm.trans primitiveAxisMonodromy.val).trans
          normalizedDevelopment).toEquiv with
        isometry_toFun := actual_deck_development_isometry Sigma.fst
          normalizedDevelopment normalizedDevelopment_metric primitiveAxisMonodromy.val
          (fun x => hqc.map_smul primitiveAxisMonodromy) }
    have primitiveGeometricDeck_period (t : ℝ) :
        primitiveGeometricDeck (verticalPath t)=verticalPath (t+primitiveCurvePeriod) := by
      change normalizedDevelopment (primitiveAxisMonodromy •
        normalizedDevelopment.symm (verticalPath t))=_
      rw [primitiveAxisMonodromy_action,normalizedDevelopment.apply_symm_apply]
    have primitiveGeometricDeck_dilation : ∀z : H2,
        (primitiveGeometricDeck z).re=Real.exp primitiveCurvePeriod*z.re ∧
        (primitiveGeometricDeck z).im=Real.exp primitiveCurvePeriod*z.im := by
      rcases actual_translated_axis_dilation_or_glide primitiveGeometricDeck
        primitiveCurvePeriod primitiveGeometricDeck_period with hdilate | hglide
      · exact hdilate
      · exact False.elim (primitive_axis_monodromy_not_glide
          (Real.exp primitiveCurvePeriod) (Real.exp_pos _) (fun z => (hglide z).1))
    obtain ⟨primitiveMultiplicity,original_period_multiple⟩ :=
      primitiveAxisPeriods deckTranslation actualPeriod (by
        simpa only [zero_add] using normalized_original_axis_period 0)
    have primitiveMultiplicity_pos_real : (0 : ℝ) < (primitiveMultiplicity : ℝ) := by
      nlinarith [primitiveCurvePeriod_pos,actualPeriod_pos]
    have primitiveMultiplicity_pos : (0 : ℤ) < primitiveMultiplicity := by
      exact_mod_cast primitiveMultiplicity_pos_real
    have original_deck_is_primitive_power :
        deckTranslation=primitiveAxisMonodromy^primitiveMultiplicity := by
      haveI : IsCancelSMul (deck (Sigma.fst : P → A)) P := hqc.isCancelSMul
      apply IsCancelSMul.right_cancel _ _
        (normalizedDevelopment.symm (verticalPath 0))
      have hp := actual_scaled_integer_deck_equivariance primitiveAxisMonodromy
        (fun t : ℝ => normalizedDevelopment.symm (verticalPath t)) primitiveCurvePeriod
        primitiveCurvePeriod_pos.ne' (fun t => (primitiveAxisMonodromy_action t).symm)
        primitiveMultiplicity 0
      have hd := normalized_original_axis_period 0
      apply normalizedDevelopment.injective
      rw [hd,←hp,normalizedDevelopment.apply_symm_apply]
      congr 1
      simpa only [zero_add] using original_period_multiple
    let originalPlaneCoordinates : P ≃ₜ ℝ × ℝ :=
      normalizedDevelopment.trans actualLogarithmicAxisCoordinates
    have primitivePlaneTranslation (x : P) :
        originalPlaneCoordinates (primitiveAxisMonodromy • x)=
          originalPlaneCoordinates x+(primitiveCurvePeriod,0) := by
      have h := actual_logarithmic_axis_dilation primitiveGeometricDeck primitiveCurvePeriod
        primitiveGeometricDeck_dilation (normalizedDevelopment x)
      change actualLogarithmicAxisCoordinates (normalizedDevelopment
        (primitiveAxisMonodromy • normalizedDevelopment.symm (normalizedDevelopment x)))=
          actualLogarithmicAxisCoordinates (normalizedDevelopment x)+(primitiveCurvePeriod,0) at h
      rw [normalizedDevelopment.symm_apply_apply] at h
      exact h
    let originalPlaneLift : C(ℝ,ℝ × ℝ) :=
      ⟨fun t => originalPlaneCoordinates (liftedPeriodicLoop t),
        originalPlaneCoordinates.continuous.comp liftedPeriodicLoop.continuous⟩
    have originalPlaneLift_proper : IsProperMap originalPlaneLift :=
      originalPlaneCoordinates.isProperMap.comp originalLift_proper
    have originalPlaneLift_injective : Function.Injective originalPlaneLift :=
      originalPlaneCoordinates.injective.comp originalLift_injective
    have primitiveMultiplicity_toNat : (primitiveMultiplicity.toNat : ℝ)=
        (primitiveMultiplicity : ℝ) := by
      have hz : (primitiveMultiplicity.toNat : ℤ)=primitiveMultiplicity := by omega
      exact_mod_cast hz
    have originalPlaneLift_period : ∀k : ℤ, ∀t : ℝ,
        originalPlaneLift (t+(k:ℝ)*1)=originalPlaneLift t+
          ((k:ℝ)*(primitiveMultiplicity.toNat:ℝ)*primitiveCurvePeriod,
           (k:ℝ)*(primitiveMultiplicity.toNat:ℝ)*0) := by
      intro k t
      change originalPlaneCoordinates (liftedPeriodicLoop (t+(k:ℝ)*1))=_
      rw [mul_one,actual_integer_deck_equivariance deckTranslation liftedPeriodicLoop
        liftedPeriodicLoop_deck_period,original_deck_is_primitive_power,←_root_.zpow_mul]
      rw [actual_translation_power_coordinates primitiveAxisMonodromy
        originalPlaneCoordinates primitiveCurvePeriod 0 primitivePlaneTranslation]
      rw [primitiveMultiplicity_toNat]
      simp only [Int.cast_mul,mul_zero]
      congr 1
      ext <;> simp only [Prod.fst,Prod.snd] <;> ring
    have originalPlaneLift_root_meeting : ¬Disjoint (Set.range originalPlaneLift)
        ((fun z : ℝ × ℝ => z+(primitiveCurvePeriod,0)) '' Set.range originalPlaneLift) :=
      CurveComplexGenusTwo.Topology.PuncturedTorusCandidate.periodic_proper_line_meets_root_translate
        originalPlaneLift originalPlaneLift_proper originalPlaneLift_injective
        1 primitiveCurvePeriod 0 (by norm_num) (Or.inl primitiveCurvePeriod_pos.ne')
        primitiveMultiplicity.toNat (by omega) originalPlaneLift_period
    have primitive_monodromy_stabilizes_original_lift :
        primitiveAxisMonodromy • liftedPeriodicLoop 0 ∈ Set.range liftedPeriodicLoop := by
      obtain ⟨z,⟨s,hs⟩,w,⟨u,rfl⟩,hu⟩ := Set.not_disjoint_iff.mp originalPlaneLift_root_meeting
      have hmeet : liftedPeriodicLoop s=primitiveAxisMonodromy • liftedPeriodicLoop u := by
        apply originalPlaneCoordinates.injective
        change originalPlaneLift s=originalPlaneCoordinates
          (primitiveAxisMonodromy • liftedPeriodicLoop u)
        rw [primitivePlaneTranslation]
        exact hs.trans hu.symm
      rcases originalLift_deck_dichotomy primitiveAxisMonodromy with hd | he
      · exact False.elim ((Set.disjoint_left.mp hd) (Set.mem_range_self s)
          ⟨liftedPeriodicLoop u,Set.mem_range_self u,hmeet.symm⟩)
      · exact he.symm.subset ⟨liftedPeriodicLoop 0,Set.mem_range_self 0,rfl⟩
    obtain ⟨originalPrimitivePower,originalPrimitivePower_eq⟩ :=
      original_deck_stabilizer_monodromy primitiveAxisMonodromy
        primitive_monodromy_stabilizes_original_lift
    have actualPeriod_eq_primitiveCurvePeriod : actualPeriod=primitiveCurvePeriod := by
      have ht := primitiveAxisMonodromy_action 0
      rw [originalPrimitivePower_eq] at ht
      have hp := actual_scaled_integer_deck_equivariance deckTranslation
        (fun t : ℝ => normalizedDevelopment.symm (verticalPath t)) actualPeriod
        actualPeriod_pos.ne' (fun t => by
          apply normalizedDevelopment.injective
          rw [normalized_original_axis_period,normalizedDevelopment.apply_symm_apply])
        originalPrimitivePower 0
      have hv : verticalPath ((originalPrimitivePower:ℝ)*actualPeriod)=
          verticalPath primitiveCurvePeriod := by
        apply normalizedDevelopment.symm.injective
        simpa only [zero_add] using hp.trans ht
      have hper : (originalPrimitivePower:ℝ)*actualPeriod=primitiveCurvePeriod :=
        verticalPath_isometry.injective hv
      have hm : (originalPrimitivePower:ℝ)*(primitiveMultiplicity:ℝ)=1 := by
        rw [original_period_multiple] at hper
        nlinarith [primitiveCurvePeriod_pos]
      have hmz : originalPrimitivePower*primitiveMultiplicity=1 := by exact_mod_cast hm
      have hkpos_real : (0:ℝ)<(originalPrimitivePower:ℝ) := by
        nlinarith [actualPeriod_pos,primitiveCurvePeriod_pos]
      have hkpos : (0:ℤ)<originalPrimitivePower := by exact_mod_cast hkpos_real
      have hmone : primitiveMultiplicity=1 := by
        have hh := mul_nonneg (show 0≤originalPrimitivePower-1 by omega)
          primitiveMultiplicity_pos.le
        nlinarith
      simpa only [hmone,Int.cast_one,one_mul] using original_period_multiple
    have primitive_circle_coordinate_scaled (t : ℝ) :
        AddCircle.homeomorphCircle primitiveCurvePeriod_pos.ne'
          ((t*primitiveCurvePeriod:ℝ):AddCircle primitiveCurvePeriod)=
        circleCoordinate (t:AddCircle (1:ℝ)) := by
      rw [AddCircle.homeomorphCircle_apply,AddCircle.toCircle_apply_mk]
      rw [AddCircle.homeomorphCircle_apply,AddCircle.toCircle_apply_mk]
      congr 1
      field_simp [primitiveCurvePeriod_pos.ne']
    have representative_eq_primitive_curve :
        (geodesicRepresentative : Circle→E)=primitiveAxisCurve.map := by
      funext z
      obtain ⟨t,ht⟩ := QuotientAddGroup.mk_surjective (circleCoordinate.symm z)
      have hz : circleCoordinate (t:AddCircle (1:ℝ))=z := by
        rw [ht,circleCoordinate.apply_symm_apply]
      rw [←hz,geodesicRepresentative_clock,actualPeriod_eq_primitiveCurvePeriod]
      change (development.symm (actualAxis (t*primitiveCurvePeriod))).1.val=
        (primitiveAxisCurveA (circleCoordinate (t:AddCircle (1:ℝ)))).val
      rw [←primitive_circle_coordinate_scaled,primitiveAxisCurveA_clock]
      change (development.symm (actualAxis (t*primitiveCurvePeriod))).1.val=
        (development.symm (normalizingIsometry (verticalPath (t*primitiveCurvePeriod)))).1.val
      have hn : normalizingIsometry (verticalPath (t*primitiveCurvePeriod))=
          actualAxis (t*primitiveCurvePeriod) := normalizer_axis _
      rw [hn]
    rw [representative_eq_primitive_curve]
    exact primitiveAxisCurve.embedded
  · intro h hfree hgeodesic
    obtain ⟨homotopy,homotopy_zero,homotopy_one⟩ := hfree
    have homotopy_component : Set.range homotopy ⊆ A := by
      have hrange := (isConnected_range homotopy.continuous).subset_connectedComponent
        (Set.mem_range_self (1, (0 : Interval)))
      have hanchor : homotopy (1, (0 : Interval)) = f 1 := homotopy_zero 1
      change Set.range homotopy ⊆ connectedComponent (f 1)
      simpa only [hanchor] using hrange
    letI : ContractibleSpace Interval :=
      (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0,by constructor <;> norm_num⟩
    letI : LocallyPathConnectedSpace Interval :=
      (isQuotientMap_projIcc (a := (0 : ℝ)) (b := 1) (h := zero_le_one)).locallyPathConnectedSpace
    let componentHomotopy : C(ℝ × Interval,A) :=
      ⟨fun ts => ⟨homotopy (circleCoordinate (ts.1 : AddCircle (1 : ℝ)),ts.2),
          homotopy_component (Set.mem_range_self _)⟩,
        (homotopy.continuous.comp
          ((circleCoordinate.continuous.comp
            ((AddCircle.continuous_mk' 1).comp continuous_fst)).prodMk continuous_snd)).subtype_mk _⟩
    have componentHomotopy_bottom (t : ℝ) : componentHomotopy (t,0) = periodicLoop t := by
      apply Subtype.ext
      exact homotopy_zero _
    have componentHomotopy_initial : (liftedPeriodicLoop 0).1 = componentHomotopy (0,0) := by
      rw [componentHomotopy_bottom]
      exact liftedPeriodicLoop_projection 0
    obtain ⟨liftedHomotopy,liftedHomotopy_spec,liftedHomotopy_unique⟩ :=
      actualCoveringMap.existsUnique_continuousMap_lifts componentHomotopy (0,0)
        (liftedPeriodicLoop 0) componentHomotopy_initial
    have liftedHomotopy_bottom : (fun t : ℝ => liftedHomotopy (t,0)) = liftedPeriodicLoop := by
      refine actualCoveringMap.eq_of_comp_eq
        (liftedHomotopy.continuous.comp (continuous_id.prodMk continuous_const))
        liftedPeriodicLoop.continuous ?_ 0 ?_
      · funext t
        exact (congrFun liftedHomotopy_spec.2 (t,0)).trans
          ((componentHomotopy_bottom t).trans (liftedPeriodicLoop_projection t).symm)
      · exact liftedHomotopy_spec.1
    have componentHomotopy_period (t : ℝ) (s : Interval) :
        componentHomotopy (t+1,s) = componentHomotopy (t,s) := by
      apply Subtype.ext
      change homotopy (circleCoordinate ((t+1 : ℝ) : AddCircle (1 : ℝ)),s) = _
      rw [AddCircle.coe_add,AddCircle.coe_period,add_zero]
      rfl
    have liftedHomotopy_deck :
        (fun ts : ℝ × Interval => liftedHomotopy (ts.1+1,ts.2)) =
          (fun ts : ℝ × Interval => deckTranslation.val (liftedHomotopy ts)) := by
      refine actualCoveringMap.eq_of_comp_eq
        (liftedHomotopy.continuous.comp
          ((continuous_fst.add continuous_const).prodMk continuous_snd))
        (deckTranslation.val.continuous.comp liftedHomotopy.continuous) ?_ (0,0) ?_
      · funext ts
        change (liftedHomotopy (ts.1+1,ts.2)).1 =
          (deckTranslation.val (liftedHomotopy ts)).1
        change (liftedHomotopy (ts.1+1,ts.2)).1 =
          (deckTranslation • liftedHomotopy ts).1
        rw [hqc.map_smul]
        exact (congrFun liftedHomotopy_spec.2 (ts.1+1,ts.2)).trans
          ((componentHomotopy_period ts.1 ts.2).trans
            (congrFun liftedHomotopy_spec.2 ts).symm)
      · change liftedHomotopy (0+1,0) = deckTranslation.val (liftedHomotopy (0,0))
        rw [show (0:ℝ)+1=1 by ring,
          congrFun liftedHomotopy_bottom 1,congrFun liftedHomotopy_bottom 0]
        exact hdeckTranslation.symm
    have competitor_component (z : Circle) : h z ∈ A :=
      homotopy_component ⟨(z,(1 : Interval)),homotopy_one z⟩
    obtain ⟨competitorPath,competitorPeriod,competitorCoordinate,competitorPeriod_pos,
      competitorPath_continuous,competitorPath_periodic,competitorPath_parametrization,
      competitorPath_local_unit⟩ := hgeodesic
    have competitorPath_component (t : ℝ) : competitorPath t ∈ A := by
      rw [competitorPath_parametrization]
      exact competitor_component _
    let componentCompetitorPath : C(ℝ,A) :=
      ⟨fun t => ⟨competitorPath t,competitorPath_component t⟩,
        competitorPath_continuous.subtype_mk _⟩
    have actual_circle_homeomorphism_lift (φ : Circle ≃ₜ Circle) :
        ∃ ψ : ℝ ≃ₜ ℝ, ∀ t : ℝ, Circle.exp (ψ t) = φ (Circle.exp t) := by
      let f : C(ℝ, Circle) := ⟨fun t => φ (Circle.exp t),
        φ.continuous.comp Circle.exp.continuous⟩
      obtain ⟨a, ha⟩ := Circle.exp_surjective (f 0)
      obtain ⟨F, hF, _⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts f 0 a ha
      let g : C(ℝ, Circle) := ⟨fun t => φ.symm (Circle.exp t),
        φ.symm.continuous.comp Circle.exp.continuous⟩
      have hg : Circle.exp 0 = g a := by
        change Circle.exp 0 = φ.symm (Circle.exp a)
        rw [ha]
        exact (φ.symm_apply_apply (Circle.exp 0)).symm
      obtain ⟨G, hG, _⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts g a 0 hg
      have hFl (t : ℝ) : Circle.exp (F t) = φ (Circle.exp t) := congrFun hF.2 t
      have hGl (t : ℝ) : Circle.exp (G t) = φ.symm (Circle.exp t) := congrFun hG.2 t
      have hGF : (fun t => G (F t)) = id := by
        refine Circle.isCoveringMap_exp.eq_of_comp_eq (G.continuous.comp F.continuous) continuous_id ?_ 0 ?_
        · funext t
          change Circle.exp (G (F t)) = Circle.exp t
          rw [hGl, hFl]
          exact φ.symm_apply_apply _
        · change G (F 0) = 0
          rw [hF.1, hG.1]
      have hFG : (fun t => F (G t)) = id := by
        refine Circle.isCoveringMap_exp.eq_of_comp_eq (F.continuous.comp G.continuous) continuous_id ?_ a ?_
        · funext t
          change Circle.exp (F (G t)) = Circle.exp t
          rw [hFl, hGl]
          exact φ.apply_symm_apply _
        · change F (G a) = a
          rw [hG.1, hF.1]
      let ψ : ℝ ≃ₜ ℝ :=
        { toFun := F
          invFun := G
          left_inv := fun t => congrFun hGF t
          right_inv := fun t => congrFun hFG t
          continuous_toFun := F.continuous
          continuous_invFun := G.continuous }
      exact ⟨ψ, fun t => congrFun hF.2 t⟩

    have circle_lift_integer_drift (φ : Circle ≃ₜ Circle) (ψ : ℝ ≃ₜ ℝ)
        (hψ : ∀ t : ℝ, Circle.exp (ψ t) = φ (Circle.exp t)) :
        ∃ n : ℤ, ∀ t : ℝ, ψ (t+2*Real.pi) = ψ t + (n:ℝ)*(2*Real.pi) := by
      have hbase : Circle.exp (ψ (2*Real.pi)) = Circle.exp (ψ 0) := by
        rw [hψ,hψ,Circle.exp_two_pi,Circle.exp_zero]
      obtain ⟨n,hn⟩ := Circle.exp_eq_exp.mp hbase
      refine ⟨n,?_⟩
      have heq : (fun t : ℝ => ψ (t+2*Real.pi)) =
          (fun t : ℝ => ψ t+(n:ℝ)*(2*Real.pi)) := by
        refine Circle.isCoveringMap_exp.eq_of_comp_eq
          (ψ.continuous.comp (continuous_id.add continuous_const))
          (ψ.continuous.add continuous_const) ?_ 0 ?_
        · funext t
          change Circle.exp (ψ (t+2*Real.pi)) = Circle.exp (ψ t+(n:ℝ)*(2*Real.pi))
          rw [hψ,Circle.exp_add_two_pi,Circle.exp_add,Circle.exp_int_mul_two_pi,mul_one,hψ]
        · simpa only [zero_add] using hn
      exact fun t => congrFun heq t

    have actual_circle_lift_unit_degree (φ : Circle ≃ₜ Circle) (ψ : ℝ ≃ₜ ℝ)
        (hψ : ∀ t : ℝ, Circle.exp (ψ t) = φ (Circle.exp t)) :
        ∃ n : ℤ, (n = 1 ∨ n = -1) ∧
          ∀ t : ℝ, ψ (t+2*Real.pi) = ψ t+(n:ℝ)*(2*Real.pi) := by
      obtain ⟨n,hn⟩ := circle_lift_integer_drift φ ψ hψ
      have hinverse (t : ℝ) : Circle.exp (ψ.symm t) = φ.symm (Circle.exp t) := by
        have h := congrArg φ.symm (hψ (ψ.symm t))
        simpa only [ψ.apply_symm_apply,φ.symm_apply_apply] using h.symm
      obtain ⟨m,hm⟩ := circle_lift_integer_drift φ.symm ψ.symm hinverse
      let error (t : ℝ) := ψ t-(n:ℝ)*t
      have hperiodic : Function.Periodic error (2*Real.pi) := by
        intro t
        dsimp [error]
        rw [hn]
        ring
      have hshift := hperiodic.zsmul m (ψ.symm 0)
      have hshift' : ψ (ψ.symm 0+(m:ℝ)*(2*Real.pi)) =
          ψ (ψ.symm 0)+(n:ℝ)*(m:ℝ)*(2*Real.pi) := by
        dsimp [error] at hshift
        simp only [zsmul_eq_mul] at hshift
        linarith
      have hone : (n:ℝ)*(m:ℝ) = 1 := by
        rw [← hm 0,ψ.apply_symm_apply,ψ.apply_symm_apply] at hshift'
        have hp := Real.pi_pos
        nlinarith
      have hint : n*m=1 := by exact_mod_cast hone
      have hnunit : n=1 ∨ n= -1 := by
        rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hint with h | h
        · exact Or.inl h.1
        · exact Or.inr h.1
      exact ⟨n,hnunit,hn⟩
    obtain ⟨competitorAngularLift,competitorAngularLift_spec⟩ :=
      actual_circle_homeomorphism_lift competitorCoordinate
    obtain ⟨competitorDegree,competitorDegree_unit,competitorAngularLift_period⟩ :=
      actual_circle_lift_unit_degree competitorCoordinate competitorAngularLift
        competitorAngularLift_spec
    let competitorCoverTime (t : ℝ) :=
      competitorAngularLift (2*Real.pi*t/competitorPeriod)/(2*Real.pi)
    have competitorCoverTime_continuous : Continuous competitorCoverTime :=
      (competitorAngularLift.continuous.comp
        ((continuous_const.mul continuous_id).div_const _)).div_const _
    let alignedCompetitorLift : C(ℝ,P) :=
      ⟨fun t => liftedHomotopy (competitorCoverTime t,1),
        liftedHomotopy.continuous.comp
          (competitorCoverTime_continuous.prodMk continuous_const)⟩
    have alignedCompetitorLift_projection (t : ℝ) :
        (alignedCompetitorLift t).1 = componentCompetitorPath t := by
      rw [show (alignedCompetitorLift t).1 = componentHomotopy (competitorCoverTime t,1)
        from congrFun liftedHomotopy_spec.2 (competitorCoverTime t,1)]
      apply Subtype.ext
      change homotopy (circleCoordinate (competitorCoverTime t : AddCircle (1 : ℝ)),1) =
        competitorPath t
      have htop : homotopy (circleCoordinate (competitorCoverTime t : AddCircle (1 : ℝ)), (1 : Interval)) =
          h (circleCoordinate (competitorCoverTime t : AddCircle (1 : ℝ))) := homotopy_one _
      rw [htop]
      have hclock : circleCoordinate (competitorCoverTime t : AddCircle (1 : ℝ)) =
          competitorCoordinate (Circle.exp (2*Real.pi*t/competitorPeriod)) := by
        change AddCircle.homeomorphCircle one_ne_zero
          (competitorCoverTime t : AddCircle (1 : ℝ)) = _
        rw [AddCircle.homeomorphCircle_apply,AddCircle.toCircle_apply_mk]
        have hscale : 2*Real.pi/(1:ℝ)*competitorCoverTime t =
            competitorAngularLift (2*Real.pi*t/competitorPeriod) := by
          dsimp [competitorCoverTime]
          field_simp [Real.pi_ne_zero]
        rw [hscale]
        exact competitorAngularLift_spec _
      rw [hclock]
      exact (competitorPath_parametrization t).symm
    let competitorInitial := alignedCompetitorLift 0
    have competitorInitial_projection : competitorInitial.1 = componentCompetitorPath 0 :=
      alignedCompetitorLift_projection 0

    obtain ⟨competitorLift,competitorLift_spec,competitorLift_unique⟩ :=
      actualCoveringMap.existsUnique_continuousMap_lifts componentCompetitorPath 0
        competitorInitial competitorInitial_projection
    have competitorLift_aligned : competitorLift = alignedCompetitorLift := by
      exact (competitorLift_unique alignedCompetitorLift
        ⟨rfl,by funext t; exact alignedCompetitorLift_projection t⟩).symm
    have competitorLift_projection (t : ℝ) : (competitorLift t).1.val = competitorPath t :=
      congrArg Subtype.val (congrFun competitorLift_spec.2 t)
    let competitorDevelopment : C(ℝ,H2) :=
      ⟨fun t => development (competitorLift t),development.continuous.comp competitorLift.continuous⟩
    have actual_competitor_development_locally_unit (t : ℝ) :
        ∃ ε : ℝ, 0 < ε ∧ ∀ s u : ℝ, |s-t| < ε → |u-t| < ε →
          dist (competitorDevelopment s) (competitorDevelopment u) = |s-u| := by
      obtain ⟨ε₀,hε₀,hunit⟩ := competitorPath_local_unit t
      obtain ⟨U,hU,htU,hmetric⟩ := development_metric (competitorLift t)
      have hopen : IsOpen (competitorLift ⁻¹' U) := hU.preimage competitorLift.continuous
      obtain ⟨ε₁,hε₁,hball⟩ := Metric.isOpen_iff.mp hopen t htU
      refine ⟨min ε₀ ε₁,lt_min hε₀ hε₁,?_⟩
      intro s u hs hu
      have hsU : competitorLift s ∈ U :=
        hball (by simpa only [Metric.mem_ball,Real.dist_eq] using hs.trans_le (min_le_right _ _))
      have huU : competitorLift u ∈ U :=
        hball (by simpa only [Metric.mem_ball,Real.dist_eq] using hu.trans_le (min_le_right _ _))
      change dist (development (competitorLift s)) (development (competitorLift u)) = |s-u|
      rw [← hmetric (competitorLift s) hsU (competitorLift u) huU,
        competitorLift_projection,competitorLift_projection]
      exact hunit s u (hs.trans_le (min_le_left _ _)) (hu.trans_le (min_le_left _ _))
    have competitorDevelopment_isometry : Isometry competitorDevelopment :=
      actual_h2_local_unit_geodesic_isometry competitorDevelopment
        competitorDevelopment.continuous actual_competitor_development_locally_unit
    have competitorCoverTime_period (t : ℝ) :
        competitorCoverTime (t+competitorPeriod) =
          competitorCoverTime t+(competitorDegree:ℝ) := by
      have htime : 2*Real.pi*(t+competitorPeriod)/competitorPeriod =
          2*Real.pi*t/competitorPeriod+2*Real.pi := by
        field_simp [competitorPeriod_pos.ne'] <;> ring
      dsimp [competitorCoverTime]
      rw [htime,competitorAngularLift_period]
      field_simp [Real.pi_ne_zero] <;> ring
    have competitor_actual_deck_period : ∃ length : ℝ, length ≠ 0 ∧
        ∀ t : ℝ, geometricDeck (competitorDevelopment t) =
          competitorDevelopment (t+length) := by
      rcases competitorDegree_unit with hn | hn
      · refine ⟨competitorPeriod,competitorPeriod_pos.ne',?_⟩
        intro t
        change development (deckTranslation.val
          (development.symm (development (competitorLift t)))) =
          development (competitorLift (t+competitorPeriod))
        rw [development.symm_apply_apply,competitorLift_aligned]
        apply congrArg development
        change deckTranslation.val (liftedHomotopy (competitorCoverTime t,1)) =
          liftedHomotopy (competitorCoverTime (t+competitorPeriod),1)
        rw [competitorCoverTime_period,hn]
        simpa only [Int.cast_one] using
          (congrFun liftedHomotopy_deck (competitorCoverTime t,1)).symm
      · refine ⟨-competitorPeriod,neg_ne_zero.mpr competitorPeriod_pos.ne',?_⟩
        intro t
        have htime : competitorCoverTime t =
            competitorCoverTime (t-competitorPeriod)-1 := by
          have hp := competitorCoverTime_period (t-competitorPeriod)
          rw [sub_add_cancel,hn] at hp
          simpa only [Int.cast_neg,Int.cast_one,← sub_eq_add_neg] using hp
        have hdeck := congrFun liftedHomotopy_deck (competitorCoverTime t, (1 : Interval))
        have htime' : competitorCoverTime t+1 = competitorCoverTime (t-competitorPeriod) := by
          linarith
        rw [htime'] at hdeck
        change development (deckTranslation.val
          (development.symm (development (competitorLift t)))) =
          development (competitorLift (t+ -competitorPeriod))
        rw [development.symm_apply_apply,competitorLift_aligned]
        apply congrArg development
        change deckTranslation.val (liftedHomotopy (competitorCoverTime t,1)) =
          liftedHomotopy (competitorCoverTime (t+ -competitorPeriod),1)
        simpa only [← sub_eq_add_neg] using hdeck.symm
    obtain ⟨competitorSignedPeriod,competitorSignedPeriod_ne,competitorDeckTranslation⟩ :=
      competitor_actual_deck_period
    have hplanes : Set.range actualAxis = Set.range competitorDevelopment :=
      actual_h2_translated_isometric_lines_same_range geometricDeckIsometry actualAxis
        competitorDevelopment actualAxis_isometry competitorDevelopment_isometry
        coverRadius coverRadius_pos actual_positive_uniform_deck_displacement actualPeriod
        competitorSignedPeriod actualPeriod_pos.ne' competitorSignedPeriod_ne
        actualAxis_translation competitorDeckTranslation
    have hsourceRange : Set.range competitorPath =
        Set.range (fun t : ℝ => (developedProjection (actualAxis t)).val) := by
      apply Set.Subset.antisymm
      · rintro _ ⟨t,rfl⟩
        obtain ⟨u,hu⟩ := hplanes.symm.subset (Set.mem_range_self t)
        refine ⟨u,?_⟩
        change (developedProjection (actualAxis u)).val = competitorPath t
        rw [hu]
        change (development.symm (development (competitorLift t))).1.val = competitorPath t
        rw [development.symm_apply_apply,competitorLift_projection]
      · rintro _ ⟨t,rfl⟩
        obtain ⟨u,hu⟩ := hplanes.subset (Set.mem_range_self t)
        refine ⟨u,?_⟩
        change competitorPath u = (developedProjection (actualAxis t)).val
        rw [← hu]
        change competitorPath u =
          (development.symm (development (competitorLift u))).1.val
        rw [development.symm_apply_apply,competitorLift_projection]
    have hcompetitorRange : Set.range h = Set.range competitorPath := by
      apply Set.Subset.antisymm
      · rintro _ ⟨z,rfl⟩
        obtain ⟨θ,hθ⟩ := Circle.exp_surjective (competitorCoordinate.symm z)
        let t : ℝ := θ*competitorPeriod/(2*Real.pi)
        have htime : 2*Real.pi*t/competitorPeriod = θ := by
          dsimp [t]
          field_simp [competitorPeriod_pos.ne',Real.pi_ne_zero]
        refine ⟨t,?_⟩
        rw [competitorPath_parametrization,htime,hθ,competitorCoordinate.apply_symm_apply]
      · rintro _ ⟨t,rfl⟩
        exact ⟨competitorCoordinate (Circle.exp (2*Real.pi*t/competitorPeriod)),
          (competitorPath_parametrization t).symm⟩
    exact hcompetitorRange.trans (hsourceRange.trans geodesicRepresentative_range.symm)




end CurveComplex.Hyperbolic
