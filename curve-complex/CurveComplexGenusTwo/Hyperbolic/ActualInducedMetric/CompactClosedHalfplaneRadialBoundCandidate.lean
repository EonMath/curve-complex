import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.EuclideanHexagonRadialBoundCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactDiscHalfplaneRegionCandidate

namespace CurveComplex.Hyperbolic

set_option maxHeartbeats 1000000 in
theorem regular_hexagon_closed_side_disc_radial_bound (w : ℂ)
    (hw : Complex.normSq w ≤ 1) (hside : ∀ i : Fin 6, 0 ≤ regularHexagonSideEquation i w) :
    Complex.normSq w ≤ regularHexagonRadius ^ 2 := by
  let α := (1 + regularHexagonRadius ^ 2) / (3 * regularHexagonRadius)
  let n := Complex.normSq w
  let L := (n+1)/3
  have hα : α ^ 2 = 2/3 := regular_hexagon_side_scale_identity
  have H (i : Fin 6) :
      0 ≤ n - 2 * (star ((α : ℂ) * (idealHexagonVertex i + idealHexagonVertex (i+1))) * w).re + 1 := hside i
  have H₀ := H 0
  have H₁ := H 1
  have H₂ := H 2
  have H₃ := H 3
  have H₄ := H 4
  have H₅ := H 5
  norm_num [idealHexagonVertex, Complex.star_def, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im] at H₀ H₁ H₂ H₃ H₄ H₅
  have hbound : (α*w.re)^2 + (α*w.im)^2 ≤ L^2 := by
    apply euclidean_six_support_radial_bound (α*w.re) (α*w.im) L <;> dsimp [L] <;>
      nlinarith [H₀,H₁,H₂,H₃,H₄,H₅]
  have hnorm : (α*w.re)^2 + (α*w.im)^2 = α^2*n := by
    dsimp [n]; simp only [Complex.normSq_apply]; ring
  rw [hnorm,hα] at hbound
  dsimp [L] at hbound
  have hq : 0 ≤ n^2-4*n+1 := by nlinarith [hbound]
  change n ≤ regularHexagonRadius ^ 2
  rw [regularHexagonRadius_sq]
  have hs : (Real.sqrt 3)^2 = 3 := by norm_num
  have hp : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  by_contra h
  have hneg : (n-(2-Real.sqrt 3)) * (n-(2+Real.sqrt 3)) < 0 :=
    mul_neg_of_pos_of_neg (by linarith) (by dsimp [n]; linarith [hw])
  nlinarith [hneg, hs]

end CurveComplex.Hyperbolic
