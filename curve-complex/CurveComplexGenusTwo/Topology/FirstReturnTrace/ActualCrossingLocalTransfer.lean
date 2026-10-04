import CurveComplexGenusTwo.Topology.FirstReturnCorner.ActualRetainedBranchCharts
namespace CurveComplex
open Set Topology
/-- Preserve an actual source crossing under equality of the second curve's
local image in an actual open neighborhood. -/
theorem source_crossing_transfer_local_trace
    {S : Type} [TopologicalSpace S]
    {a c d : Curve S} {p : S} (hp : CrossesAt a c p)
    (U : Set S) (hU : IsOpen U) (hpU : p ∈ U)
    (htrace : ∀ x ∈ U, x ∈ d.image ↔ x ∈ c.image) : CrossesAt a d p := by
  obtain ⟨E,hpE,hEU,hE0,ha,hc⟩ := source_crossing_open_partial_chart hp U hU hpU
  refine ⟨E.source,E.target,hpE,E.toHomeomorphSourceTarget,E.open_source,E.open_target,?_,?_⟩
  · exact hE0
  · intro x hx
    exact ⟨ha x hx,(htrace x (hEU hx)).trans (hc x hx)⟩
end CurveComplex
#print axioms CurveComplex.source_crossing_transfer_local_trace
