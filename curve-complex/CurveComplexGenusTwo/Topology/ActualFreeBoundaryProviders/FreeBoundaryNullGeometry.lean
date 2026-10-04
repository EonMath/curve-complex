import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalDiskContainment

namespace CoherentEndpointMotion.FreeBoundaryNullGeometry
open CurveComplex Set Topology

/-- Initial ordinary boundary geometry and its nullhomotopy in the actual
caller subset; no embedded disk is assumed. -/
structure NullBigonBoundary {X : Type} [TopologicalSpace X]
    (B : Set X) (a b : C(Interval,X)) where
  first : C(Interval,X)
  second : C(Interval,X)
  first_embedded : IsEmbedding first
  second_embedded : IsEmbedding second
  first_on_a : range first ⊆ range a
  second_on_b : range second ⊆ range b
  zero_eq : first 0 = second 0
  one_eq : first 1 = second 1
  corners_off_boundary : first 0 ∉ B ∧ first 1 ∉ B
  sides_inter : range first ∩ range second = {first 0,first 1}
  loop : Curve X
  loop_image : loop.image = range first ∪ range second
  loop_null : (⟨loop.map,loop.embedded.continuous⟩ : C(Circle,X)).Nullhomotopic

/-- Initial three-side boundary geometry and its nullhomotopy in the actual
caller subset; both free endpoints and the literal B-side are retained. -/
structure NullHalfBigonBoundary {X : Type} [TopologicalSpace X]
    (B : Set X) (a b : C(Interval,X)) where
  first : C(Interval,X)
  second : C(Interval,X)
  boundarySide : C(Interval,X)
  first_embedded : IsEmbedding first
  second_embedded : IsEmbedding second
  boundary_embedded : IsEmbedding boundarySide
  first_on_a : range first ⊆ range a
  second_on_b : range second ⊆ range b
  first_zero_boundary : first 0 ∈ B
  second_zero_boundary : second 0 ∈ B
  corner_eq : first 1 = second 1
  corner_off_boundary : first 1 ∉ B
  first_interior : ∀ t ∈ Ioo (0 : Interval) 1, first t ∉ B
  second_interior : ∀ t ∈ Ioo (0 : Interval) 1, second t ∉ B
  boundary_in_B : ∀ t, boundarySide t ∈ B
  boundary_zero : boundarySide 0 = first 0
  boundary_one : boundarySide 1 = second 0
  sides_inter : range first ∩ range second = {first 1}
  loop : Curve X
  loop_image : loop.image = range first ∪ range second ∪ range boundarySide
  loop_null : (⟨loop.map,loop.embedded.continuous⟩ : C(Circle,X)).Nullhomotopic

end CoherentEndpointMotion.FreeBoundaryNullGeometry
