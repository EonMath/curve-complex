import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactVertexReflections

namespace CurveComplex.Hyperbolic

private theorem refl_isometry_apply (z : H2) : IsometryEquiv.refl H2 z = z := rfl

theorem unitCircleReflection_positive_real_iff (z : H2) :
    0 < (unitCircleReflectionEquiv z).re ↔ 0 < z.re := by
  rw [unitCircleReflection_re]
  exact div_pos_iff_of_pos_right (by nlinarith [z.im_pos])

theorem unitCircleReflection_nonnegative_real_iff (z : H2) :
    0 ≤ (unitCircleReflectionEquiv z).re ↔ 0 ≤ z.re := by
  rw [unitCircleReflection_re]
  have hd : 0 < z.re ^ 2 + z.im ^ 2 := by nlinarith [z.im_pos]
  rw [le_div_iff₀ hd]
  simp only [zero_mul]

theorem unitCircleReflection_closed_inner_iff_outer (z : H2) :
    (unitCircleReflectionEquiv z).re ^ 2 + (unitCircleReflectionEquiv z).im ^ 2 ≤ 1 ↔
      1 ≤ z.re ^ 2 + z.im ^ 2 := by
  rw [unitCircleReflection_normSq]
  have hd : 0 < z.re ^ 2 + z.im ^ 2 := by nlinarith [z.im_pos]
  rw [div_le_iff₀ hd]
  simp only [one_mul]

noncomputable def quarterOrientationIsometry (positive inner : Bool) : H2 ≃ᵢ H2 :=
  (if positive then IsometryEquiv.refl H2 else verticalReflectionEquiv).trans
    (if inner then IsometryEquiv.refl H2 else unitCircleReflectionEquiv)

theorem quarterOrientation_strict (positive inner : Bool) (z : H2) :
    (0 < (quarterOrientationIsometry positive inner z).re ∧
      (quarterOrientationIsometry positive inner z).re ^ 2 +
        (quarterOrientationIsometry positive inner z).im ^ 2 < 1) ↔
    (if positive then 0 < z.re else z.re < 0) ∧
      (if inner then z.re ^ 2 + z.im ^ 2 < 1 else 1 < z.re ^ 2 + z.im ^ 2) := by
  cases positive <;> cases inner <;>
    simp [quarterOrientationIsometry, IsometryEquiv.trans_apply, refl_isometry_apply,
      unitCircleReflection_positive_real_iff, unitCircleReflection_inner_iff_outer,
      verticalReflection_re, verticalReflection_im, neg_sq]

theorem quarterOrientation_closed (positive inner : Bool) (z : H2) :
    (0 ≤ (quarterOrientationIsometry positive inner z).re ∧
      (quarterOrientationIsometry positive inner z).re ^ 2 +
        (quarterOrientationIsometry positive inner z).im ^ 2 ≤ 1) ↔
    (if positive then 0 ≤ z.re else z.re ≤ 0) ∧
      (if inner then z.re ^ 2 + z.im ^ 2 ≤ 1 else 1 ≤ z.re ^ 2 + z.im ^ 2) := by
  cases positive <;> cases inner <;>
    simp [quarterOrientationIsometry, IsometryEquiv.trans_apply, refl_isometry_apply,
      unitCircleReflection_nonnegative_real_iff, unitCircleReflection_closed_inner_iff_outer,
      verticalReflection_re, verticalReflection_im, neg_sq]

theorem quarterOrientation_fixes_normalized_vertex (positive inner : Bool) (p : H2)
    (hp : p.re = 0) (hi : p.im = 1) : quarterOrientationIsometry positive inner p = p := by
  have hv := (verticalReflection_fixed_iff p).mpr hp
  have hn := (unitCircleReflection_fixed_iff p).mpr (by rw [hp, hi]; norm_num)
  cases positive <;> cases inner <;>
    simp [quarterOrientationIsometry, IsometryEquiv.trans_apply, refl_isometry_apply, hv, hn]

end CurveComplex.Hyperbolic
