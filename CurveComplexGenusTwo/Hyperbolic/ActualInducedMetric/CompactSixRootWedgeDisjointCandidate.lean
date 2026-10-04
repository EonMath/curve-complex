import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactCanonicalReflectionCandidate
namespace CurveComplex.Hyperbolic

set_option maxHeartbeats 2000000 in
theorem six_root_open_wedge_unique (w : ℂ) (i j : Fin 6)
    (hi : Real.sqrt 3*|(star (idealHexagonVertex i)*w).im| < (star (idealHexagonVertex i)*w).re)
    (hj : Real.sqrt 3*|(star (idealHexagonVertex j)*w).im| < (star (idealHexagonVertex j)*w).re) : i=j := by
  have hp : 0<Real.sqrt 3 := by positivity
  have hs : (Real.sqrt 3)^2=3 := by norm_num
  have hiplus : Real.sqrt 3*(star (idealHexagonVertex i)*w).im < (star (idealHexagonVertex i)*w).re :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (le_abs_self _) hp.le) hi
  have himinus : -Real.sqrt 3*(star (idealHexagonVertex i)*w).im < (star (idealHexagonVertex i)*w).re := by
    have h := lt_of_le_of_lt (mul_le_mul_of_nonneg_left (neg_le_abs _) hp.le) hi
    nlinarith
  have hjplus : Real.sqrt 3*(star (idealHexagonVertex j)*w).im < (star (idealHexagonVertex j)*w).re :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (le_abs_self _) hp.le) hj
  have hjminus : -Real.sqrt 3*(star (idealHexagonVertex j)*w).im < (star (idealHexagonVertex j)*w).re := by
    have h := lt_of_le_of_lt (mul_le_mul_of_nonneg_left (neg_le_abs _) hp.le) hj
    nlinarith
  have hix : 0<(star (idealHexagonVertex i)*w).re := lt_of_le_of_lt (by positivity) hi
  have hjx : 0<(star (idealHexagonVertex j)*w).re := lt_of_le_of_lt (by positivity) hj
  have hx := congrArg (fun a : ℝ => a*w.re) hs
  have hy := congrArg (fun a : ℝ => a*w.im) hs
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals norm_num [idealHexagonVertex,Complex.star_def,Complex.mul_re,Complex.mul_im,
    Complex.conj_re,Complex.conj_im] at hiplus himinus hjplus hjminus hix hjx
  all_goals nlinarith [hx,hy]

end CurveComplex.Hyperbolic
