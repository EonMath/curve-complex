import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactHalfTurnLocalCover
import CurveComplexGenusTwo.Hyperbolic.Cayley

namespace CurveComplex.Hyperbolic

 theorem vertexHalfTurn_coe (z : H2) :
    (vertexHalfTurnEquiv z : ℂ) = -(z : ℂ)⁻¹ := by
  apply Complex.ext
  · change (verticalReflectionEquiv (unitCircleReflectionEquiv z)).re = _
    rw [verticalReflection_re, unitCircleReflection_re]
    simp only [Complex.neg_re, Complex.inv_re, Complex.normSq_apply, UpperHalfPlane.re, UpperHalfPlane.im, pow_two, neg_div, neg_neg]
  · change (verticalReflectionEquiv (unitCircleReflectionEquiv z)).im = _
    rw [verticalReflection_im, unitCircleReflection_im]
    simp only [Complex.neg_im, Complex.inv_im, neg_neg, Complex.normSq_apply, UpperHalfPlane.re, UpperHalfPlane.im, pow_two, neg_div, neg_neg]

theorem cayley_halfTurn (z : H2) :
    (cayley (vertexHalfTurnEquiv z) : ℂ) = -(cayley z : ℂ) := by
  have hz : (z : ℂ) ≠ 0 := UpperHalfPlane.ne_zero z
  have hden : (z : ℂ) + Complex.I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at hi
    change z.im + 1 = 0 at hi
    linarith [z.im_pos]
  have hden' : -(z : ℂ)⁻¹ + Complex.I ≠ 0 := by
    rw [← vertexHalfTurn_coe]
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at hi
    change (vertexHalfTurnEquiv z).im + 1 = 0 at hi
    linarith [(vertexHalfTurnEquiv z).im_pos]
  change (((vertexHalfTurnEquiv z : H2) : ℂ) - Complex.I) /
    (((vertexHalfTurnEquiv z : H2) : ℂ) + Complex.I) = -(((z : ℂ) - Complex.I) / ((z : ℂ) + Complex.I))
  rw [vertexHalfTurn_coe]
  apply (div_eq_iff hden').mpr
  field_simp [hz, hden]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem cayley_square_fibers (a b : H2) :
    (cayley a : ℂ) ^ 2 = (cayley b : ℂ) ^ 2 ↔
      toHalfTurnMetricCone a = toHalfTurnMetricCone b := by
  rw [halfTurnMetricCone_eq_iff, sq_eq_sq_iff_eq_or_eq_neg]
  constructor
  · rintro (h | h)
    · exact Or.inl (cayley_injective (Subtype.ext h))
    · apply Or.inr
      apply cayley_injective
      apply Subtype.ext
      rw [cayley_halfTurn]
      exact h
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (cayley_halfTurn b)

end CurveComplex.Hyperbolic
