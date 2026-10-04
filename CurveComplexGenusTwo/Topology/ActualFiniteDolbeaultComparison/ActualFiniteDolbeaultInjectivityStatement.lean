import CurveComplexGenusTwo.Topology.ActualFiniteDolbeaultComparison.CechDolbeaultComparison

open scoped Manifold ContDiff Bundle

namespace CanonicalDimensionTwo

universe v

/-- Injectivity of the specified actual finite-cover Čech–Dolbeault map.
This needs no Leray hypothesis: a global primitive of the image corrects
the local partition primitives into actual holomorphic zero-cochains.
The definition is a source-review candidate, not a proof. -/
def ActualFiniteDolbeaultInjectivityStatement
    (E : Type) [TopologicalSpace E] [T2Space E] [CompactSpace E]
    [Nonempty E] [PreconnectedSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] : Prop :=
  ∀ (U : SameAtlasAnalyticCohomology.OpenCover.{0, v} E) [Fintype U.Index]
    (P : SameAtlasAnalyticCohomology.SubordinateSmoothPartition U),
      Function.Injective (SameAtlasAnalyticCohomology.cechDolbeaultComparison U P)

end CanonicalDimensionTwo
