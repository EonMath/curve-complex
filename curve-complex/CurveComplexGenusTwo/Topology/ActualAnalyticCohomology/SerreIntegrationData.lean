import CurveComplexGenusTwo.Topology.ActualAnalyticCohomology.AnalyticCechAlgebra
import CurveComplexGenusTwo.Topology.ActualAnalyticCohomology.ChartFrameTransition
import CurveComplexGenusTwo.Topology.ActualAnalyticCohomology.SmoothJetTopology
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import CurveComplexGenusTwo.Topology.ActualLocalAnalyticSheaves.LocalSheafScaffold
import CurveComplexGenusTwo.Topology.ActualIntervalLocalComparison.ActualOneFormBridge
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

open TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Bundle Topology
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1000000

namespace SameAtlasAnalyticCohomology
universe u v
variable {E : Type u} [TopologicalSpace E] [ChartedSpace ℂ E]
  [IsManifold 𝓘(ℂ) ∞ E]

variable (U : OpenCover E)

structure SubordinateSmoothPartition (U : OpenCover E) [Fintype U.Index] where
  weight : U.Index → E → ℝ
  smoothWeight : ∀ i a, ContDiffOn ℝ ∞
    (fun z : ℂ => weight i ((extChartAt 𝓘(ℂ) a).symm z))
    (extChartAt 𝓘(ℂ) a).target
  nonnegativeWeight : ∀ i x, 0 ≤ weight i x
  supportWeight : ∀ i, tsupport (weight i) ⊆ (U.opens i : Set E)
  partitionOne : ∀ x, (∑ i, weight i x) = 1



structure SerreIntegrationData (U : OpenCover E) [Fintype U.Index]
    [MeasurableSpace E] where
  partition : SubordinateSmoothPartition U
  areaMeasure : Measure E
  areaNonzero : areaMeasure Set.univ ≠ 0
  chartDensity : E → ℂ → ℝ
  chartDensity_pos : ∀ a z, z ∈ (extChartAt 𝓘(ℂ) a).target → 0 < chartDensity a z
  chartDensity_smooth : ∀ a, ContDiffOn ℝ ∞ (chartDensity a)
    (extChartAt 𝓘(ℂ) a).target
  chartDensityTransition : ∀ a b x,
    x ∈ (extChartAt 𝓘(ℂ) a).source →
    x ∈ (extChartAt 𝓘(ℂ) b).source →
    chartDensity b ((extChartAt 𝓘(ℂ) b) x) =
      chartDensity a ((extChartAt 𝓘(ℂ) a) x) /
        ‖chartTransitionDerivative a b x‖ ^ 2
  areaChartFormula : ∀ a : E,
    let c := extChartAt 𝓘(ℂ) a
    Measure.map c (areaMeasure.restrict c.source) =
      (volume.withDensity (fun z : ℂ =>
        ENNReal.ofReal (chartDensity a z))).restrict c.target
  integrableWedge : ∀ (α : SmoothZeroOne E) (s : ActualCanonicalSection E),
    Integrable (fun x => (2 * Complex.I) * α.1 x x *
      chartCanonicalCoefficient x x s /
        (chartDensity x ((extChartAt 𝓘(ℂ) x) x) : ℂ)) areaMeasure

/-- Local coordinate wedge, normalized to the specified area measure.
`d(bar z) ∧ dz = 2i dx ∧ dy`. -/

noncomputable def normalizedWedgeInChart [Fintype U.Index]
    [MeasurableSpace E] (D : SerreIntegrationData U)
    (a x : E) (α : SmoothZeroOne E) (s : ActualCanonicalSection E) : ℂ :=
  (2 * Complex.I) * α.1 a x * chartCanonicalCoefficient a x s /
    (D.chartDensity a ((extChartAt 𝓘(ℂ) a) x) : ℂ)



end SameAtlasAnalyticCohomology
