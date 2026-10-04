import CurveComplexGenusTwo.Dictionary.BranchedCover
import Mathlib.MeasureTheory.Measure.Hausdorff

namespace CurveComplex
open Set MeasureTheory
open scoped MeasureTheory NNReal ENNReal

theorem BranchedDoubleCover.actual_ramification_finite {E S : Type*}
    [TopologicalSpace E] [TopologicalSpace S] (q : BranchedDoubleCover E S) :
    q.ramification.Finite := by
  apply Set.Finite.of_injOn (f := q.projection) (t := (q.branch : Set S))
  · intro x hx; exact hx
  · intro x hx y hy hxy
    rcases (q.fiber_pair x y).mp hxy with h | h
    · exact h.symm
    · rw [(q.fixed_iff_branch x).mpr hx] at h
      exact h.symm
  · exact q.branch.finite_toSet

end CurveComplex

namespace CurveComplex.Hyperbolic
open Set MeasureTheory
open scoped MeasureTheory NNReal ENNReal

theorem finite_set_normalized_area_zero {E : Type*} [MetricSpace E]
    [MeasurableSpace E] [BorelSpace E] (s : Set E) (hs : s.Finite) :
    (μHE[2] : Measure E) s = 0 := by
  letI : NullSingletonClass (Measure.hausdorffMeasure 2 : Measure E) :=
    Measure.nullSingletonClass_hausdorff E (by norm_num)
  have h : (Measure.hausdorffMeasure 2 : Measure E) s = 0 := hs.measure_zero _
  unfold Measure.euclideanHausdorffMeasure
  simp only [Measure.smul_apply]
  norm_num only [Nat.cast_ofNat] at *
  rw [h, smul_zero]

end CurveComplex.Hyperbolic
