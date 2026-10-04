import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactCanonicalRotationAreaCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactHalfplaneJordanIdentificationCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.VerticalReflectionCrossing

namespace CurveComplex.Hyperbolic

theorem vertical_reflection_cayley_conjugate (z : H2) :
    (cayley (verticalReflectionEquiv z) : ℂ) = star (cayley z : ℂ) := by
  apply Complex.ext
  · simp only [cayley,Complex.div_re,Complex.normSq_apply,Complex.sub_re,
      Complex.sub_im,Complex.add_re,Complex.add_im,Complex.I_re,Complex.I_im,
      UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,verticalReflection_re,verticalReflection_im,Complex.star_def,Complex.conj_re,
      sub_zero,add_zero]
    ring
  · simp only [cayley,Complex.div_im,Complex.normSq_apply,Complex.sub_re,
      Complex.sub_im,Complex.add_re,Complex.add_im,Complex.I_re,Complex.I_im,
      UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,verticalReflection_re,verticalReflection_im,Complex.star_def,Complex.conj_im,
      sub_zero,add_zero]
    ring

theorem regular_hexagon_reflection_side (i : Fin 6) (w : ℂ) :
    regularHexagonSideEquation i (star w) = regularHexagonSideEquation (5-i) w := by
  let α := (1+regularHexagonRadius^2)/(3*regularHexagonRadius)
  change Complex.normSq (star w) - 2*(star ((α:ℂ)*(idealHexagonVertex i+idealHexagonVertex (i+1)))*star w).re+1 =
    Complex.normSq w - 2*(star ((α:ℂ)*(idealHexagonVertex (5-i)+idealHexagonVertex (5-i+1)))*w).re+1
  fin_cases i <;> norm_num [idealHexagonVertex,Complex.star_def,Complex.normSq_apply,
    Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im] <;> ring

theorem regular_hexagon_reflection_mem_interior (z : H2) :
    verticalReflectionEquiv z ∈ regularHexagonRegion.interior ↔
      z ∈ regularHexagonRegion.interior := by
  rw [← regular_hexagon_actual_halfplane_eq_jordan_interior]
  change (∀i,0<regularHexagonSideEquation i (cayley (verticalReflectionEquiv z):ℂ)) ↔
    (∀i,0<regularHexagonSideEquation i (cayley z:ℂ))
  simp_rw [vertical_reflection_cayley_conjugate,regular_hexagon_reflection_side]
  constructor
  · intro h i
    have hi : (5-(5-i) : Fin 6)=i := by omega
    simpa only [hi] using h (5-i)
  · intro h i; exact h (5-i)

end CurveComplex.Hyperbolic
