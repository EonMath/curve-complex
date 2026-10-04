import CurveComplexGenusTwo.Topology.FirstReturnCorner.ActualRetainedBranchCharts
import CurveComplexGenusTwo.Foundations.FoundationsIntersectionPort

namespace CurveComplex
open Set Topology Schoenflies
set_option maxHeartbeats 4000000

/-- Whole-curve image agreement in an actual open neighborhood transfers the
literal local coordinate crossing, without assuming new transversality. -/
theorem crossesAt_of_curve_images_agree_on_open
    {E : Type} [TopologicalSpace E] [ChartedSpace Plane E] [ClosedSurface E]
    (a b c d : Curve E) (p : E) (U : Set E) (hU : IsOpen U) (hpU : p ∈ U)
    (ha : ∀ x ∈ U, x ∈ a.image ↔ x ∈ c.image)
    (hb : ∀ x ∈ U, x ∈ b.image ↔ x ∈ d.image)
    (hp : CrossesAt c d p) : CrossesAt a b p := by
  obtain ⟨F,hpF,hFU,hF0,hFc,hFd⟩ := source_crossing_open_partial_chart hp U hU hpU
  refine ⟨F.source,F.target,hpF,F.toHomeomorphSourceTarget,F.open_source,F.open_target,hF0,?_⟩
  intro x hx
  exact ⟨(ha x (hFU hx)).trans (hFc x hx),(hb x (hFU hx)).trans (hFd x hx)⟩

end CurveComplex
