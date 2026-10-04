import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactSupportingGeodesicCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.HyperbolicGeodesicAreaNullCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactCanonicalRadialPieceIsometryCandidate

namespace CurveComplex.Hyperbolic
open Set MeasureTheory
open scoped MeasureTheory NNReal ENNReal

theorem hyperbolic_semicircle_normalized_area_zero (c r : ℝ) (hr : 0<r) :
    (μHE[2] : Measure H2) {z | (z.re-c)^2+z.im^2=r^2}=0 := by
  obtain ⟨e,he⟩ := supporting_semicircle_vertical_isometry c r hr
  have hs : {z : H2 | (z.re-c)^2+z.im^2=r^2} = e.symm '' {z | z.re=0} := by
    ext z
    constructor
    · intro hz
      exact ⟨e z,(he z).mp hz,e.symm_apply_apply z⟩
    · rintro ⟨y,hy,rfl⟩
      apply (he (e.symm y)).mpr
      simpa only [e.apply_symm_apply] using (show y.re=0 from hy)
  rw [hs]
  exact isometric_vertical_geodesic_normalized_area_zero 0 e.symm

theorem cayley_imaginary_zero_iff (z : H2) :
    (cayley z : ℂ).im=0 ↔ z.re=0 := by
  have hd : z.re^2+(z.im+1)^2 ≠ 0 := ne_of_gt (by nlinarith [z.im_pos,sq_nonneg z.re])
  have hi : (cayley z : ℂ).im = -2*z.re/(z.re^2+(z.im+1)^2) := by
    simp only [cayley,Complex.div_im,Complex.normSq_apply,Complex.sub_re,
      Complex.sub_im,Complex.add_re,Complex.add_im,Complex.I_re,Complex.I_im,
      sub_zero,add_zero,←pow_two,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
    field_simp
    ring
  rw [hi,div_eq_zero_iff]
  simp only [hd,or_false]
  constructor <;> intro h <;> linarith

theorem cayley_radial_linear_zero_iff (z : H2) (k : ℝ) :
    (cayley z : ℂ).re=k*(cayley z : ℂ).im ↔
      (z.re+k)^2+z.im^2=1+k^2 := by
  let D := z.re^2+(z.im+1)^2
  have hd : D≠0 := ne_of_gt (by dsimp [D]; nlinarith [z.im_pos,sq_nonneg z.re])
  have hi : (cayley z : ℂ).im=-2*z.re/D := by
    simp only [cayley,Complex.div_im,Complex.normSq_apply,Complex.sub_re,
      Complex.sub_im,Complex.add_re,Complex.add_im,Complex.I_re,Complex.I_im,
      sub_zero,add_zero,←pow_two,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
    dsimp [D];field_simp;ring
  have hr : (cayley z : ℂ).re=(z.re^2+z.im^2-1)/D := by
    simp only [cayley,Complex.div_re,Complex.normSq_apply,Complex.sub_re,
      Complex.sub_im,Complex.add_re,Complex.add_im,Complex.I_re,Complex.I_im,
      sub_zero,add_zero,←pow_two,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
    dsimp [D];field_simp;ring
  rw [hi,hr]
  have hm : k*(-2*z.re/D)=(k*(-2*z.re))/D := by ring
  rw [hm,div_left_inj' hd]
  constructor <;> intro h <;> nlinarith

theorem cayley_half_wedge_boundaries_normalized_area_zero :
    (μHE[2] : Measure H2) {z | (cayley z : ℂ).im=0 ∨
      (cayley z : ℂ).re=Real.sqrt 3*|(cayley z : ℂ).im|}=0 := by
  have hsub : {z : H2 | (cayley z : ℂ).im=0 ∨
      (cayley z : ℂ).re=Real.sqrt 3*|(cayley z : ℂ).im|} ⊆
      {z : H2 | z.re=0} ∪ {z | (z.re+Real.sqrt 3)^2+z.im^2=4} ∪
      {z | (z.re-Real.sqrt 3)^2+z.im^2=4} := by
    intro z hz
    rcases hz with hi|hr
    · exact Or.inl (Or.inl ((cayley_imaginary_zero_iff z).mp hi))
    · by_cases hy : 0≤(cayley z : ℂ).im
      · rw [abs_of_nonneg hy] at hr
        have h := (cayley_radial_linear_zero_iff z (Real.sqrt 3)).mp hr
        norm_num at h
        exact Or.inl (Or.inr h)
      · rw [abs_of_neg (lt_of_not_ge hy)] at hr
        have h := (cayley_radial_linear_zero_iff z (-Real.sqrt 3)).mp (by linarith)
        norm_num at h
        exact Or.inr (show (z.re-Real.sqrt 3)^2+z.im^2=4 from by simpa only [sub_eq_add_neg] using h)
  have h₀ : (μHE[2] : Measure H2) {z | z.re=0}=0 := by
    have h := isometric_vertical_geodesic_normalized_area_zero 0 (IsometryEquiv.refl H2)
    change (μHE[2] : Measure H2) (id '' {z | z.re=0})=0 at h
    simpa only [image_id] using h
  have h₁ := hyperbolic_semicircle_normalized_area_zero (-Real.sqrt 3) 2 (by norm_num)
  have h₂ := hyperbolic_semicircle_normalized_area_zero (Real.sqrt 3) 2 (by norm_num)
  norm_num only [neg_neg,sub_neg_eq_add,show (2:ℝ)^2=4 by norm_num] at h₁ h₂
  apply measure_mono_null hsub
  exact measure_union_null (measure_union_null h₀ h₁) h₂

end CurveComplex.Hyperbolic
