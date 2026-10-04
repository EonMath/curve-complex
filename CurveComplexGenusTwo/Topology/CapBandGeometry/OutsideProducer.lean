import CurveComplexGenusTwo.Topology.CapBandGeometry.OutsideDiskFill

open Set Topology
namespace CurveComplex
private abbrev Plane := EuclideanSpace ℝ (Fin 2)
private abbrev UnitDisk := Metric.closedBall (0 : Plane) 1
private def diskInterior : Set UnitDisk :=
  {x | (x : Plane) ∈ Metric.ball 0 1}
private def diskBoundary : Set UnitDisk :=
  {x | (x : Plane) ∈ Metric.sphere 0 1}

theorem actual_band_outside_disk_fills_complement
    {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    {g : ℕ} (hg : 2 ≤ g) (hS : IsGenus S g)
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (B : CompatibleOutsideBands D) {c : Curve S}
    (hfront : frontier
      (Set.range D.square ∪ Set.range B.first ∪ Set.range B.second) = c.image)
    (f : C(UnitDisk, S)) (hf : IsEmbedding f)
    (hboundary : f '' diskBoundary = c.image)
    (houtside : f '' diskInterior ⊆ interior
      (Set.range D.square ∪ Set.range B.first ∪ Set.range B.second)ᶜ) :
    (Set.range D.square ∪ Set.range B.first ∪ Set.range B.second) ∪
      Set.range f = Set.univ := by
  obtain ⟨hclosed⟩ := hS.2.1
  letI : ClosedSurface S := hclosed
  exact CapBandGeometry.actual_band_outside_fill D B hfront f hf hboundary houtside

#print axioms actual_band_outside_disk_fills_complement
end CurveComplex
