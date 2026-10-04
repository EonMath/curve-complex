import Mathlib

namespace CurveComplex.Hyperbolic
open Filter Topology MeasureTheory
open scoped MeasureTheory

-- Verbatim reuse of the APPROVED normalized source definition.
-- Integration must import the canonical existing declaration.
def ConeAngleAt (X : Type*) [MetricSpace X] (x : X) (θ : ℝ) : Prop :=
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  Tendsto (fun r : ℝ =>
    (μH[1] (Metric.sphere x r)).toReal / r)
    (𝓝[>] (0 : ℝ)) (nhds θ)

end CurveComplex.Hyperbolic
