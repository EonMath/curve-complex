import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

open TopologicalSpace
open scoped Manifold ContDiff Bundle
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1000000

namespace SameAtlasAnalyticCohomology
universe u v
variable {E : Type u} [TopologicalSpace E] [ChartedSpace ℂ E]
  [IsManifold 𝓘(ℂ) ∞ E]

/-- The derivative `dw/dz` of two charts in the original complex atlas. -/
noncomputable def chartTransitionDerivative (a b x : E) : ℂ :=
  (fderiv ℂ ((extChartAt 𝓘(ℂ) b) ∘ (extChartAt 𝓘(ℂ) a).symm)
    ((extChartAt 𝓘(ℂ) a) x)) 1


end SameAtlasAnalyticCohomology
