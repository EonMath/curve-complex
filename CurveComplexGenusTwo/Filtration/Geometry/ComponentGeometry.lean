import CurveComplexGenusTwo.Filtration.Geometry.ActualArcFiltrationV3
import CurveComplexGenusTwo.Filtration.Geometry.MarkedArcPrimitives

namespace CurveComplex.HyperellipticModel
open Set

variable {X : Type} [TopologicalSpace X]

/-- The maximal-component predicate is the canonical connected component in the complement. -/
theorem complementComponent_iff_componentIn {A U : Set X} :
    IsComplementComponent A U ↔
      ∃ x ∈ Aᶜ, U = connectedComponentIn Aᶜ x := by
  constructor
  · rintro ⟨⟨x, hx⟩, hU, hsub, hmax⟩
    have hxc : x ∈ Aᶜ := hsub hx
    refine ⟨x, hxc, ?_⟩
    exact (hmax _ (isConnected_connectedComponentIn_iff.mpr hxc)
      (hU.isPreconnected.subset_connectedComponentIn hx hsub)
      (connectedComponentIn_subset _ _)).symm
  · rintro ⟨x, hx, rfl⟩
    have hc : IsConnected (connectedComponentIn Aᶜ x) :=
      isConnected_connectedComponentIn_iff.mpr hx
    refine ⟨hc.nonempty, hc, connectedComponentIn_subset _ _, ?_⟩
    intro V hV hsub hVA
    apply Subset.antisymm
    · exact hV.isPreconnected.subset_connectedComponentIn
        (hsub (mem_connectedComponentIn hx)) hVA
    · exact hsub

/-- Distinct complementary components are disjoint, without choosing names. -/
theorem complementComponents_disjoint {A U V : Set X}
    (hU : IsComplementComponent A U) (hV : IsComplementComponent A V)
    (hne : U ≠ V) : Disjoint U V := by
  apply Set.disjoint_left.mpr
  intro x hxU hxV
  have hu : U = connectedComponentIn Aᶜ x := by
    exact (hU.2.2.2 _ (isConnected_connectedComponentIn_iff.mpr (hU.2.2.1 hxU))
      (hU.2.1.isPreconnected.subset_connectedComponentIn hxU hU.2.2.1)
      (connectedComponentIn_subset _ _)).symm
  have hv : V = connectedComponentIn Aᶜ x := by
    exact (hV.2.2.2 _ (isConnected_connectedComponentIn_iff.mpr (hV.2.2.1 hxV))
      (hV.2.1.isPreconnected.subset_connectedComponentIn hxV hV.2.2.1)
      (connectedComponentIn_subset _ _)).symm
  exact hne (hu.trans hv.symm)

/-- In a locally connected surface, faces of a closed graph are open. -/
theorem complementComponent_open [LocallyConnectedSpace X] {A U : Set X}
    (hA : IsClosed A) (hU : IsComplementComponent A U) : IsOpen U := by
  obtain ⟨x, _, rfl⟩ := complementComponent_iff_componentIn.mp hU
  exact hA.isOpen_compl.connectedComponentIn

/-- The boundary of an open complementary component lies on the graph. -/
theorem complementComponent_frontier_subset [LocallyConnectedSpace X] {A U : Set X}
    (hA : IsClosed A) (hU : IsComplementComponent A U) : frontier U ⊆ A := by
  intro x hx
  by_contra hxa
  let V := connectedComponentIn Aᶜ x
  have hxV : x ∈ V := mem_connectedComponentIn hxa
  have hV : IsComplementComponent A V :=
    complementComponent_iff_componentIn.mpr ⟨x, hxa, rfl⟩
  have hopenV : IsOpen V := complementComponent_open hA hV
  have hcl : x ∈ closure U := frontier_subset_closure hx
  obtain ⟨y, hyV, hyU⟩ := (mem_closure_iff.mp hcl) V hopenV hxV
  have heq : U = V := by
    by_contra hne
    exact Set.disjoint_left.mp (complementComponents_disjoint hU hV hne) hyU hyV
  have hxU : x ∈ U := heq.symm ▸ hxV
  have hxi : x ∈ interior U := by rw [(complementComponent_open hA hU).interior_eq]; exact hxU
  exact ((mem_frontier_iff_notMem_interior hxU).mp hx) hxi

/-- A gap remains a face of a larger graph when the added graph misses its interior. -/
theorem complementComponent_of_graph_enlargement {A B U : Set X}
    (hU : IsComplementComponent A U) (hAB : A ⊆ B) (hUB : Disjoint U B) :
    IsComplementComponent B U := by
  refine ⟨hU.1, hU.2.1, ?_, ?_⟩
  · intro x hx
    exact Set.disjoint_left.mp hUB hx
  · intro V hV hUV hVB
    exact hU.2.2.2 V hV hUV (fun x hx ha => hVB hx (hAB ha))


/-- Source Lemma 9.8's component placement, once the actual punctured object is connected. -/
theorem connected_object_in_unique_gap {A B : Set X}
    (hB : IsConnected (B \ A)) (hdense : B ⊆ closure (B \ A)) :
    ∃! U : Set X, IsComplementComponent A U ∧ B \ A ⊆ U ∧ B ⊆ closure U := by
  obtain ⟨x, hx⟩ := hB.nonempty
  let U := connectedComponentIn Aᶜ x
  have hU : IsComplementComponent A U :=
    complementComponent_iff_componentIn.mpr ⟨x, hx.2, rfl⟩
  have hsub : B \ A ⊆ U := hB.isPreconnected.subset_connectedComponentIn hx
    (fun _ hy => hy.2)
  refine ⟨U, ⟨hU, hsub, hdense.trans (closure_mono hsub)⟩, ?_⟩
  intro V hV
  have hxV : x ∈ V := hV.2.1 hx
  by_contra hne
  exact Set.disjoint_left.mp (complementComponents_disjoint hV.1 hU hne)
    hxV (mem_connectedComponentIn hx.2)


/-- The original downstairs sphere has locally connected topology, independently of smoothing. -/
theorem actualSphere_locallyConnected {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] (M : HyperellipticModel E S) :
    LocallyConnectedSpace S := by
  letI : LocallyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 2)) _
  exact M.sphere.locallyConnectedSpace

/-- Every face of the actual finite representative graph is open with boundary on that graph. -/
theorem actualFamily_face_open_frontier {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] (M : HyperellipticModel E S)
    {ι : Type*} [Finite ι] (r : ι → MarkedArc M) {U : Set S}
    (hU : IsComplementComponent (⋃ i, (r i).image) U) :
    IsOpen U ∧ frontier U ⊆ ⋃ i, (r i).image := by
  letI : T2Space S := M.sphere.symm.t2Space
  letI : LocallyConnectedSpace S := actualSphere_locallyConnected M
  have hclosed : IsClosed (⋃ i, (r i).image) := (markedFamily_graph_compact r).isClosed
  exact ⟨complementComponent_open hclosed hU, complementComponent_frontier_subset hclosed hU⟩


end CurveComplex.HyperellipticModel
