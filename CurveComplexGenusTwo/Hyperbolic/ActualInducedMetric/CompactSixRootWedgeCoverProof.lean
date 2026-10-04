import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactCanonicalRotationAreaCandidate

namespace CurveComplex.Hyperbolic

theorem six_root_open_half_wedge_cover (w : ℂ)
    (him : ∀i : Fin 6, (star (idealHexagonVertex i)*w).im ≠ 0)
    (hboundary : ∀i : Fin 6, (star (idealHexagonVertex i)*w).re ≠
      Real.sqrt 3*|(star (idealHexagonVertex i)*w).im|) :
    ∃i : Fin 6, Real.sqrt 3*|(star (idealHexagonVertex i)*w).im| <
      (star (idealHexagonVertex i)*w).re := by
  classical
  have hp : 0 < Real.sqrt 3 := by positivity
  have hs : (Real.sqrt 3)^2 = 3 := by norm_num
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun j : Fin 6 => (star (idealHexagonVertex j)*w).re) Finset.univ_nonempty
  refine ⟨i, lt_of_le_of_ne ?_ (hboundary i).symm⟩
  have h0 := hmax (0 : Fin 6) (Finset.mem_univ _)
  have h1 := hmax (1 : Fin 6) (Finset.mem_univ _)
  have h2 := hmax (2 : Fin 6) (Finset.mem_univ _)
  have h3 := hmax (3 : Fin 6) (Finset.mem_univ _)
  have h4 := hmax (4 : Fin 6) (Finset.mem_univ _)
  have h5 := hmax (5 : Fin 6) (Finset.mem_univ _)
  have hx := congrArg (fun a : ℝ => a*w.re) hs
  have hy := congrArg (fun a : ℝ => a*w.im) hs
  rcases le_total 0 ((star (idealHexagonVertex i)*w).im) with hpos | hneg
  · rw [abs_of_nonneg hpos]
    fin_cases i <;> norm_num [idealHexagonVertex, Complex.star_def, Complex.mul_re,
      Complex.mul_im, Complex.conj_re, Complex.conj_im] at h0 h1 h2 h3 h4 h5 ⊢
    all_goals nlinarith [hx, hy]
  · rw [abs_of_nonpos hneg]
    fin_cases i <;> norm_num [idealHexagonVertex, Complex.star_def, Complex.mul_re,
      Complex.mul_im, Complex.conj_re, Complex.conj_im] at h0 h1 h2 h3 h4 h5 ⊢
    all_goals nlinarith [hx, hy]

end CurveComplex.Hyperbolic
