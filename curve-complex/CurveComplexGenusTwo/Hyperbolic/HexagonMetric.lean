import CurveComplexGenusTwo.Hyperbolic.HexagonCoordinates
import CurveComplexGenusTwo.Hyperbolic.DiscMetric

namespace CurveComplex.Hyperbolic

theorem regularHexagon_adjacent_cosh_dist (i : Fin 6) :
    Real.cosh (dist (regularHexagonH2Point i)
      (regularHexagonH2Point (i + 1))) =
      1 + 2 * regularHexagonRadius ^ 2 /
        ((1 - regularHexagonRadius ^ 2) ^ 2) := by
  let u : Metric.ball (0 : ℂ) 1 :=
    ⟨regularHexagonDiscPoint i, regularHexagonDiscPoint_mem_ball i⟩
  let v : Metric.ball (0 : ℂ) 1 :=
    ⟨regularHexagonDiscPoint (i + 1), regularHexagonDiscPoint_mem_ball (i + 1)⟩
  have h := cayleyInverse_cosh_dist u v
  change Real.cosh (dist (regularHexagonH2Point i)
      (regularHexagonH2Point (i + 1))) = _
  rw [show regularHexagonH2Point i = cayleyInverse u by rfl,
    show regularHexagonH2Point (i + 1) = cayleyInverse v by rfl]
  rw [h]
  change 1 + 2 * Complex.normSq (regularHexagonDiscPoint i -
      regularHexagonDiscPoint (i + 1)) /
      ((1 - Complex.normSq (regularHexagonDiscPoint i)) *
        (1 - Complex.normSq (regularHexagonDiscPoint (i + 1)))) = _
  rw [show Complex.normSq (regularHexagonDiscPoint i) =
      regularHexagonRadius ^ 2 by
        rw [Complex.normSq_eq_norm_sq, regularHexagonDiscPoint_norm],
    show Complex.normSq (regularHexagonDiscPoint (i + 1)) =
      regularHexagonRadius ^ 2 by
        rw [Complex.normSq_eq_norm_sq, regularHexagonDiscPoint_norm],
    regularHexagon_adjacent_chord_normSq]
  ring_nf

theorem regularHexagon_adjacent_cosh_dist_eq (i j : Fin 6) :
    Real.cosh (dist (regularHexagonH2Point i)
      (regularHexagonH2Point (i + 1))) =
    Real.cosh (dist (regularHexagonH2Point j)
      (regularHexagonH2Point (j + 1))) := by
  rw [regularHexagon_adjacent_cosh_dist, regularHexagon_adjacent_cosh_dist]

theorem regularHexagon_adjacent_dist_eq (i j : Fin 6) :
    dist (regularHexagonH2Point i) (regularHexagonH2Point (i + 1)) =
    dist (regularHexagonH2Point j) (regularHexagonH2Point (j + 1)) := by
  apply Real.cosh_injOn
  · exact dist_nonneg
  · exact dist_nonneg
  exact regularHexagon_adjacent_cosh_dist_eq i j

end CurveComplex.Hyperbolic
