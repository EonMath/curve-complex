import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualGlobalCoverAreaCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.InducedMetricAreaReuse

namespace CurveComplex.Hyperbolic
open Set Topology MeasureTheory
open scoped MeasureTheory NNReal ENNReal

theorem actual_compatible_branched_cover_normalized_total_area {E S B : Type}
    [TopologicalSpace E] [TopologicalSpace S] [T2Space S]
    [MetricSpace B] [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
    (m : MetricSpace E) (ht : m.toUniformSpace.toTopologicalSpace = ‹TopologicalSpace E›)
    (q : BranchedDoubleCover E S) (identify : S ≃ₜ B)
    (hlocal : ∀ x : E, x ∉ q.ramification → ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ∀ z ∈ U, m.dist y z = dist (identify (q.projection y)) (identify (q.projection z))) :
    @hausdorffArea E m = 2 * (μHE[2] : Measure B) univ := by
  cases ht
  letI : MetricSpace E := m
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  exact actual_branched_cover_normalized_total_area q identify hlocal

end CurveComplex.Hyperbolic
