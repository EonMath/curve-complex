import CurveComplexGenusTwo.Topology.ActualAnalyticCohomology.DolbeaultDbar

open scoped Manifold ContDiff
open Set Filter Topology

namespace SameAtlasAnalyticCohomology.ClosedImageReview
universe u

/-- Source-facing intermediate from the bounded holomorphic-plus-small
subsequence argument in McMullen, Theorem 8.10, pp.81–82. This is an
uninhabited statement definition. Both domain and codomain use the actual
approved all-jets topologies, and the map is the actual proved dbar. -/
def ActualDbarSmallNormalFamilyStatement : Prop :=
  ∀ (E : Type u) [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ∞ E] [T2Space E] [CompactSpace E]
    [Nonempty E] [PreconnectedSpace E]
    (f : ℕ → SmoothZero E),
    (∀ n x, ‖(f n).1 x‖ ≤ 1) →
    Tendsto (fun n => dolbeaultDbar (f n)) atTop (𝓝 0) →
    ∃ F : SmoothZero E, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (f ∘ φ) atTop (𝓝 F)

end SameAtlasAnalyticCohomology.ClosedImageReview
