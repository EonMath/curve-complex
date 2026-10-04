import CurveComplexGenusTwo.Topology.ActualNonstandardCutRegion.ForbiddenConnector
import CurveComplexGenusTwo.Filtration.Geometry.ComponentGeometry

open CurveComplex Set Topology
open CurveComplex.HyperellipticModel

namespace CurveComplexGenusTwo.SourceTopology.ThreeArcCut

/-- Every complementary region of a nonempty closed set has an actual
frontier point on that set. -/
theorem complement_component_closure_meets_forbidden
    {S : Type} [TopologicalSpace S] [ConnectedSpace S]
    [LocallyConnectedSpace S]
    (F U : Set S) (hF : IsClosed F) (hFn : F.Nonempty)
    (hU : IsComplementComponent F U) : (closure U ∩ F).Nonempty := by
  have hnot : U ≠ Set.univ := by
    intro he
    obtain ⟨x, hx⟩ := hFn
    exact hU.2.2.1 (he.symm ▸ Set.mem_univ x) hx
  obtain ⟨x, hx⟩ := nonempty_frontier_iff.mpr ⟨hU.1, hnot⟩
  exact ⟨x, frontier_subset_closure hx,
    complementComponent_frontier_subset hF hU hx⟩

/-- The exterior of one actual region remains connected because all other
regions attach to the same connected forbidden graph. -/
theorem complement_of_component_of_connected_forbidden_connected
    {S : Type} [TopologicalSpace S] [ConnectedSpace S]
    [LocallyConnectedSpace S]
    (F U : Set S) (hF : IsClosed F) (hFc : IsConnected F)
    (hU : IsComplementComponent F U) : IsConnected Uᶜ := by
  let J := {V : Set S // IsComplementComponent F V ∧ V ≠ U}
  let W : J → Set S := fun V => V.val
  have hW : ∀ V, IsConnected (W V) := fun V => V.property.1.2.1
  have hmeet : ∀ V, (closure (W V) ∩ F).Nonempty := fun V =>
    complement_component_closure_meets_forbidden F V.val hF hFc.1 V.property.1
  have hcover : Uᶜ = F ∪ ⋃ V, W V := by
    ext x
    constructor
    · intro hx
      by_cases hxF : x ∈ F
      · exact Or.inl hxF
      · let V := connectedComponentIn Fᶜ x
        have hxV : x ∈ V := mem_connectedComponentIn hxF
        have hV : IsComplementComponent F V :=
          complementComponent_iff_componentIn.mpr ⟨x, hxF, rfl⟩
        have hne : V ≠ U := fun he => hx (he ▸ hxV)
        exact Or.inr (Set.mem_iUnion.mpr ⟨⟨V, hV, hne⟩, hxV⟩)
    · rintro (hxF | hxV)
      · exact fun hxU => hU.2.2.1 hxU hxF
      · obtain ⟨V, hxV⟩ := Set.mem_iUnion.mp hxV
        exact fun hxU => Set.disjoint_left.mp
          (complementComponents_disjoint V.property.1 hU V.property.2) hxV hxU
  rw [hcover]
  exact connected_complement_of_forbidden_graph_attachments F W hFc hW hmeet

end CurveComplexGenusTwo.SourceTopology.ThreeArcCut

#print axioms CurveComplexGenusTwo.SourceTopology.ThreeArcCut.complement_of_component_of_connected_forbidden_connected
