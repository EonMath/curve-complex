import CurveComplexGenusTwo.Topology.ActualAnalyticCohomology.SmoothJetTopology
import CurveComplexGenusTwo.Topology.ActualAnalyticCohomology.ChartFrameTransition
import CurveComplexGenusTwo.Topology.ActualLocalDbarSolvability.ActualLocalDbarContracts

open TopologicalSpace SameAtlasAnalyticCohomology
open scoped Manifold ContDiff Bundle Distributions

namespace CanonicalDimensionTwo

universe u
variable {E : Type u} [TopologicalSpace E] [T2Space E]
  [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]

/-- The actual chart target, as an open subset supporting Mathlib tests. -/
noncomputable def actualChartTestOpen (a : E) : Opens ℂ :=
  ⟨(extChartAt 𝓘(ℂ) a).target, isOpen_extChartAt_target a⟩

end CanonicalDimensionTwo
