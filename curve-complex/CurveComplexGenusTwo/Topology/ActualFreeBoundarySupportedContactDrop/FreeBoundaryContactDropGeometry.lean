import CurveComplexGenusTwo.Topology.ActualRegionalContactGeometry.RegionalFiniteContactGeometry

namespace CoherentEndpointMotion.FreeBoundaryContactRepair
open CurveComplex Set Topology

/-- Actual supported contact cancellation on the literal caller subset.
The anchor remains the same comparison trace. The moving trace is the full
image of `b` under this motion. Both endpoints and the whole protected graph
are fixed by this interior move; the original class witness still permits
free endpoints. No null boundary or initial disk is a field. -/
structure SupportedContactDrop
    {S : Type} [TopologicalSpace S]
    (Q : Set S) (B : Set ↥Q) (a b : C(Interval, ↥Q))
    (protectedGraph : Set ↥Q) (contact : ↥Q) where
  support : Set ↥Q
  compactSupport : Set ↥Q
  support_open : IsOpen support
  compact_support : IsCompact compactSupport
  compact_in_support : compactSupport ⊆ support
  support_interior : support ⊆ {y : ↥Q | y.val ∈ interior Q}
  support_off_boundary : Disjoint support B
  support_off_graph : Disjoint support protectedGraph
  contact_in_support : contact ∈ support
  contact_on_original : contact ∈ range a ∩ range b
  replacement : C(Interval, ↥Q)
  replacement_embedded : IsEmbedding replacement
  replacement_zero : replacement 0 = b 0
  replacement_one : replacement 1 = b 1
  replacement_interior : ∀ t ∈ Ioo (0 : Interval) 1, replacement t ∉ B
  motion : AmbientIsotopy ↥Q
  boundary_setwise : ∀ t, (fun y => motion.map (t,y)) '' B = B
  boundary_pointwise : ∀ t y, y ∈ B → motion.map (t,y) = y
  graph_pointwise : ∀ t y, y ∈ protectedGraph → motion.map (t,y) = y
  outside_compact_support : ∀ t y, y ∉ compactSupport → motion.map (t,y) = y
  whole_moving_trace : motion.finalMap '' range b = range replacement
  whole_trace_outside_support : range replacement \ support = range b \ support
  retained_contacts : range a ∩ range replacement ⊆ range a ∩ range b
  deleted_contact : contact ∉ range replacement
  replacement_contacts_finite : (range a ∩ range replacement).Finite
  strict_contact_decrease :
    (range a ∩ range replacement).ncard < (range a ∩ range b).ncard

end CoherentEndpointMotion.FreeBoundaryContactRepair
