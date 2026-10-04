import CurveComplexGenusTwo.Topology.CapBandGeometry.CapAnnulusRetraction
open Set Topology
namespace CurveComplex
open CurveComplexGenusTwo.CWHurewicz
private abbrev Plane := EuclideanSpace ℝ (Fin 2)
private abbrev UnitDisk := Metric.closedBall (0 : Plane) 1
private def diskInterior : Set UnitDisk := {x | (x : Plane) ∈ Metric.ball 0 1}
private def diskBoundary : Set UnitDisk := {x | (x : Plane) ∈ Metric.sphere 0 1}
private def innerDisk : Set UnitDisk := {x | (x : Plane) ∈ Metric.closedBall 0 (1/2)}

theorem actual_band_cap_complement_two_generators
    {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (B : CompatibleOutsideBands D) {c : Curve S}
    (hfront : frontier
      (Set.range D.square ∪ Set.range B.first ∪ Set.range B.second) = c.image)
    (f : C(UnitDisk, S)) (hf : IsEmbedding f)
    (hboundary : f '' diskBoundary = c.image)
    (hfill : (Set.range D.square ∪ Set.range B.first ∪ Set.range B.second) ∪
      Set.range f = Set.univ) :
    ∃ p : (Fin 2 → ℤ) →ₗ[ℤ] H ↥((f '' innerDisk)ᶜ) 1,
      Function.Surjective p := by
  have houtside := (embedded_disk_side_same_map
    (Set.range D.square ∪ Set.range B.first ∪ Set.range B.second) c hfront f hf hboundary).resolve_left
      (actual_band_rejects_internal_disk D B hfront f hf hboundary)
  let e := CapBandGeometry.capExteriorNeighborhoodHomotopyEquiv
    (CapBandGeometry.bandUnion D B)
    (compatibleOutsideBands_compact_connected_cover_probe D B).1.isClosed
    c hfront f hf hboundary houtside hfill
  let eH := (CircleHomologyComputation.homotopyHomologyIso e 1).toLinearEquiv
  let p := (CapBandGeometry.actual_band_HOne_coordinates D B).symm.trans eH.symm
  exact ⟨p.toLinearMap,p.surjective⟩

theorem actual_compatible_band_disk_cap_producer
    {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    {g : ℕ} (hg : 2 ≤ g) (hS : IsGenus S g)
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (B : CompatibleOutsideBands D) {c : Curve S}
    (hfront : frontier
      (Set.range D.square ∪ Set.range B.first ∪ Set.range B.second) = c.image)
    (hbound : BoundsDisc c) :
    ∃ f : C(UnitDisk, S), IsEmbedding f ∧
      f '' diskBoundary = c.image ∧
      IsOpen (f '' innerDisk)ᶜ ∧ IsOpen (f '' diskInterior) ∧
      (f '' innerDisk)ᶜ ∪ (f '' diskInterior) = Set.univ ∧
      PathConnectedSpace ↥((f '' innerDisk)ᶜ ∩ (f '' diskInterior)) ∧
      ContractibleSpace ↥(f '' diskInterior) ∧
      ∃ p : (Fin 2 → ℤ) →ₗ[ℤ] H ↥((f '' innerDisk)ᶜ) 1,
        Function.Surjective p := by
  obtain ⟨f,hf,hboundary⟩ := hbound
  have houtside := (embedded_disk_side_same_map
    (Set.range D.square ∪ Set.range B.first ∪ Set.range B.second) c hfront f hf hboundary).resolve_left
      (actual_band_rejects_internal_disk D B hfront f hf hboundary)
  have hfill := actual_band_outside_disk_fills_complement hg hS D B hfront f hf hboundary houtside
  obtain ⟨hU,hV,hcover⟩ := embedded_disk_open_cover f hf
  obtain ⟨p,hp⟩ := actual_band_cap_complement_two_generators D B hfront f hf hboundary hfill
  exact ⟨f,hf,hboundary,hU,hV,hcover,embedded_disk_cover_overlap_pathConnected f hf,
    embedded_disk_interior_contractible f hf,p,hp⟩

#print axioms actual_band_cap_complement_two_generators
#print axioms actual_compatible_band_disk_cap_producer
end CurveComplex
