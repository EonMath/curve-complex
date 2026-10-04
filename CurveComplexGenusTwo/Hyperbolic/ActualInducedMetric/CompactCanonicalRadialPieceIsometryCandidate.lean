import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactCanonicalRadialPieceCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactCanonicalReflectionCandidate

namespace CurveComplex.Hyperbolic
open Set MeasureTheory
open scoped MeasureTheory NNReal ENNReal

theorem hyperbolic_isometry_normalized_area_image (e : H2 ≃ᵢ H2) (s : Set H2) :
    (μHE[2] : Measure H2) (e '' s) = (μHE[2] : Measure H2) s := by
  have h := e.isometry.hausdorffMeasure_image (d := 2) (Or.inl (by norm_num)) s
  letI : (Measure.hausdorffMeasure 2 : Measure (EuclideanSpace ℝ (Fin 2))).IsAddHaarMeasure := by
    simpa using (MeasureTheory.isAddHaarMeasure_hausdorffMeasure (E := EuclideanSpace ℝ (Fin 2)))
  unfold Measure.euclideanHausdorffMeasure
  simp only [Measure.smul_apply]
  norm_num only [Nat.cast_ofNat] at *
  exact congrArg (fun t : ℝ≥0∞ =>
    (Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin 2)))
      (Measure.hausdorffMeasure 2 : Measure (EuclideanSpace ℝ (Fin 2)))) • t) h

theorem regular_hexagon_radial_piece_isometric_area (e : H2 ≃ᵢ H2) :
    (μHE[2] : Measure H2) (e '' {z | z ∈ regularHexagonRegion.interior ∧
      0 < (cayley z : ℂ).im ∧ Real.sqrt 3*(cayley z : ℂ).im < (cayley z : ℂ).re}) =
      ENNReal.ofReal (Real.pi/12) := by
  rw [hyperbolic_isometry_normalized_area_image]
  exact regular_hexagon_first_radial_piece_area

end CurveComplex.Hyperbolic
