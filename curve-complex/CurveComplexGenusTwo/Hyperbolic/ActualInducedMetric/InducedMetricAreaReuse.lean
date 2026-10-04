import Mathlib

namespace CurveComplex.Hyperbolic
open MeasureTheory
open scoped MeasureTheory

noncomputable def hausdorffArea (X : Type*) [MetricSpace X] : ENNReal :=
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  μHE[2] (Set.univ : Set X)

end CurveComplex.Hyperbolic
