import CurveComplexGenusTwo.Topology.ActualMain14RelativeCancellation.RelativeOriginalInitialMarkedBigon
import CurveComplexGenusTwo.Topology.ActualMain14RelativeCancellation.RelativeBigonEmptyInteriorSelection
namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem actual_two_mark_disk_inner_or_endpoint_bigon_selection
    (M : HyperellipticModel E S) (a b : NonLoopArc M)
    (N : ArcNeighborhood a) (hb : b.image ⊆ interior N.closedSet)
    (hends : ({a.val.map 0,a.val.map 1}:Set S) = {b.val.map 0,b.val.map 1})
    (hfinite : (ArcSurgery.crossings M a.toEssential b.toEssential).Finite)
    (hcross : ∀ p ∈ ArcSurgery.crossings M a.toEssential b.toEssential,
      ArcSurgery.CrossesInDisk M a.toEssential b.toEssential p)
    (hpositive : (ArcSurgery.crossings M a.toEssential b.toEssential).Nonempty) :
    ∃ B : ActualMarkedTwoSideDisk M a.toEssential b.toEssential,
      Set.range B.disk ⊆ interior N.closedSet ∧
      Disjoint B.openInterior (a.image ∪ b.image ∪ (M.cover.branch : Set S)) ∧
      (B.firstCorner ∈ ArcSurgery.crossings M a.toEssential b.toEssential ∨
        B.secondCorner ∈ ArcSurgery.crossings M a.toEssential b.toEssential) ∧
      (∀ x ∈ ({a.val.map 0,a.val.map 1}:Set S),
        x ≠ B.firstCorner → x ≠ B.secondCorner → x ∉ Set.range B.disk) := by
  clear hcross
  obtain ⟨B,hBN,hBcontact⟩ :=
    relative_original_finite_contacts_produce_initial_marked_bigon M a b N hb hends hfinite hpositive
  exact relative_initial_marked_disk_produces_confined_empty_bigon
    M a b N hfinite B hBN (Or.inr hBcontact)

end CurveComplex.HyperellipticModel
