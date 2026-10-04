import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactActualHalfplaneRegionCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactJordanRegionUniqueness

namespace CurveComplex.Hyperbolic
open Set Topology

theorem bounded_open_connected_region_frontier_subset_jordan_eq_inside
    {C V : Set Schoenflies.Plane} (hC : Schoenflies.IsJordanCurve C)
    (hV : IsConnected V) (hopen : IsOpen V) (hbound : Bornology.IsBounded V)
    (hfront : frontier V ⊆ C) (hdis : Disjoint C V) : V = Schoenflies.inside C := by
  let hs := Schoenflies.jordan_curve_theorem hC
  have hsub : V ⊆ Cᶜ := fun x hx hxc => Set.disjoint_left.mp hdis hxc hx
  obtain ⟨x,hx⟩ := hV.nonempty
  have hxC := hsub hx
  have hcomp := hV.isPreconnected.subset_connectedComponentIn hx hsub
  have hor : x ∈ Schoenflies.inside C ∨ x ∈ Schoenflies.outside C := by
    have h := Schoenflies.inside_union_outside C
    rw [← h] at hxC; exact hxC
  rcases hor with hin | hout
  · have hVin : V ⊆ Schoenflies.inside C := by
      rw [hs.connectedComponentIn_eq_inside hin] at hcomp; exact hcomp
    have hinV : Schoenflies.inside C ⊆ V := by
      apply preconnected_subset_of_frontier_disjoint hopen hs.isConnected_inside.isPreconnected
      · exact Set.disjoint_left.mpr fun y hy hiy => Schoenflies.inside_subset_compl hiy (hfront hy)
      · exact ⟨x,hin,hx⟩
    exact subset_antisymm hVin hinV
  · have houtV : Schoenflies.outside C ⊆ V := by
      apply preconnected_subset_of_frontier_disjoint hopen hs.isConnected_outside.isPreconnected
      · exact Set.disjoint_left.mpr fun y hy hoy => Schoenflies.outside_subset_compl hoy (hfront hy)
      · exact ⟨x,hout,hx⟩
    exact False.elim (hs.not_isBounded_outside (hbound.subset houtV))

theorem regular_hexagon_actual_halfplane_eq_jordan_interior :
    regularHexagonActualHalfplaneInterior = regularHexagonRegion.interior := by
  let e := hyperbolicPlaneHomeomorph
  let C := e '' frontier regularHexagonRegion.interior
  have hJ : Schoenflies.IsJordanCurve C := by
    dsimp [C]; rw [regularHexagonRegion.boundary_is_edges]
    exact regularHexagonCandidate.embedded_boundary_isJordanCurve regularHexagonCandidate_embedded e
  have hfront : frontier (e '' regularHexagonActualHalfplaneInterior) ⊆ C := by
    rw [← e.image_frontier]
    exact image_mono regular_hexagon_actual_halfplane_frontier_subset
  have hdis : Disjoint C (e '' regularHexagonActualHalfplaneInterior) := by
    apply Set.disjoint_left.mpr
    rintro p ⟨z,hz,rfl⟩ ⟨w,hw,heq⟩
    have heq' : w = z := e.injective heq
    subst w
    rw [regularHexagonRegion.boundary_is_edges] at hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    have hp := hw i
    rw [regular_hexagon_edge_side_equation_zero i z hi] at hp
    exact (lt_irrefl 0) hp
  have hbound : Bornology.IsBounded (e '' regularHexagonActualHalfplaneInterior) := by
    have hc : IsCompact (closure regularHexagonActualHalfplaneInterior) :=
      Metric.isCompact_of_isClosed_isBounded isClosed_closure regular_hexagon_actual_halfplane_bounded.closure
    exact (hc.image e.continuous).isBounded.subset (image_mono subset_closure)
  have h := bounded_open_connected_region_frontier_subset_jordan_eq_inside hJ
    (regular_hexagon_actual_halfplane_connected.image _ e.continuous.continuousOn)
    (e.isOpenMap _ regular_hexagon_actual_halfplane_open) hbound hfront hdis
  have hR := regularHexagonRegion.image_interior_eq_inside regularHexagonCandidate_embedded e
  exact e.injective.image_injective (h.trans hR.symm)

theorem regular_hexagon_actual_halfplane_frontier_eq :
    frontier regularHexagonActualHalfplaneInterior = frontier regularHexagonRegion.interior := by
  rw [regular_hexagon_actual_halfplane_eq_jordan_interior]

end CurveComplex.Hyperbolic
