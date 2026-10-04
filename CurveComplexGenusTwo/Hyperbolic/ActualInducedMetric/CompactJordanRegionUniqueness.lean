import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.EmbeddedHexagonJordan
namespace CurveComplex.Hyperbolic
open Set Topology

theorem preconnected_subset_of_frontier_disjoint {X : Type*} [TopologicalSpace X]
    {U V : Set X} (hU : IsOpen U) (hV : IsPreconnected V)
    (hd : Disjoint (frontier U) V) (hn : (V ∩ U).Nonempty) : V ⊆ U := by
  let : PreconnectedSpace V := isPreconnected_iff_preconnectedSpace.mp hV
  have hcl := isClopen_preimage_val hU hd
  have hne : {x : V | (x : X) ∈ U}.Nonempty := by
    obtain ⟨x, hx, hu⟩ := hn
    exact ⟨⟨x, hx⟩, hu⟩
  have hall : {x : V | (x : X) ∈ U} = Set.univ := hcl.eq_univ hne
  intro x hx
  have hp : (⟨x, hx⟩ : V) ∈ {y : V | (y : X) ∈ U} := by rw [hall]; trivial
  exact hp

theorem bounded_connected_open_jordan_region_eq_inside
    {C V : Set Schoenflies.Plane} (hC : Schoenflies.IsJordanCurve C)
    (hV : IsConnected V) (hopen : IsOpen V) (hbound : Bornology.IsBounded V)
    (hfront : frontier V = C) : V = Schoenflies.inside C := by
  let hs := Schoenflies.jordan_curve_theorem hC
  have hdis : Disjoint C V := hfront ▸ (disjoint_frontier_iff_isOpen.mpr hopen)
  have hsub : V ⊆ Cᶜ := fun x hx hxc => Set.disjoint_left.mp hdis hxc hx
  obtain ⟨x, hx⟩ := hV.nonempty
  have hxC := hsub hx
  have hcomp := hV.isPreconnected.subset_connectedComponentIn hx hsub
  have hor : x ∈ Schoenflies.inside C ∨ x ∈ Schoenflies.outside C := by
    have h := Schoenflies.inside_union_outside C
    rw [← h] at hxC
    exact hxC
  rcases hor with hin | hout
  · have hVin : V ⊆ Schoenflies.inside C := by
      rw [hs.connectedComponentIn_eq_inside hin] at hcomp
      exact hcomp
    have hinV : Schoenflies.inside C ⊆ V := by
      apply preconnected_subset_of_frontier_disjoint hopen hs.isConnected_inside.isPreconnected
      · rw [hfront]
        exact Set.disjoint_left.mpr (fun y hy hiy => Schoenflies.inside_subset_compl hiy hy)
      · exact ⟨x, hin, hx⟩
    exact Set.Subset.antisymm hVin hinV
  · have houtV : Schoenflies.outside C ⊆ V := by
      apply preconnected_subset_of_frontier_disjoint hopen hs.isConnected_outside.isPreconnected
      · rw [hfront]
        exact Set.disjoint_left.mpr (fun y hy hoy => Schoenflies.outside_subset_compl hoy hy)
      · exact ⟨x, hout, hx⟩
    exact False.elim (hs.not_isBounded_outside (hbound.subset houtV))

theorem HexagonRegion.image_interior_eq_inside {P : Hexagon} (R : HexagonRegion P)
    (hP : P.IsEmbedded) (e : H2 ≃ₜ Schoenflies.Plane) :
    e '' R.interior = Schoenflies.inside (e '' frontier R.interior) := by
  apply bounded_connected_open_jordan_region_eq_inside
  · rw [R.boundary_is_edges]
    exact P.embedded_boundary_isJordanCurve hP e
  · exact R.connected_interior.image _ e.continuous.continuousOn
  · exact e.isOpenMap _ R.open_interior
  · exact ((closedPolygon_isCompact R).image e.continuous).isBounded.subset
      (Set.image_mono subset_closure)
  · exact (e.image_frontier R.interior).symm

theorem HexagonRegion.exterior_frontier_eq {P : Hexagon} (R : HexagonRegion P)
    (hP : P.IsEmbedded) : frontier ((closure R.interior)ᶜ) = frontier R.interior := by
  let e := hyperbolicPlaneHomeomorph
  let C := e '' frontier R.interior
  have hJ : Schoenflies.IsJordanCurve C := by
    dsimp [C]
    rw [R.boundary_is_edges]
    exact P.embedded_boundary_isJordanCurve hP e
  let hs := Schoenflies.jordan_curve_theorem hJ
  have hinside := R.image_interior_eq_inside hP e
  have hout : (closure (Schoenflies.inside C))ᶜ = Schoenflies.outside C := by
    rw [closure_eq_self_union_frontier, hs.frontier_inside]
    ext z
    simp only [Set.mem_compl_iff, Set.mem_union]
    dsimp [Schoenflies.inside, Schoenflies.outside]
    tauto
  have hmap : e '' ((closure R.interior)ᶜ) = Schoenflies.outside C := by
    rw [e.image_compl, e.image_closure, hinside]
    exact hout
  have hf : e '' frontier ((closure R.interior)ᶜ) = e '' frontier R.interior := by
    rw [e.image_frontier, hmap, hs.frontier_outside]
  exact e.injective.image_injective hf

end CurveComplex.Hyperbolic
