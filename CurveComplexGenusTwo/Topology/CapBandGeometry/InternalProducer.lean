import CurveComplexGenusTwo.Topology.CapBandGeometry.InternalDiskReject
open Set Topology
namespace CurveComplex
private abbrev Plane := EuclideanSpace ℝ (Fin 2)
private abbrev UnitDisk := Metric.closedBall (0 : Plane) 1
private def diskInterior : Set UnitDisk := {x | (x : Plane) ∈ Metric.ball 0 1}
private def diskBoundary : Set UnitDisk := {x | (x : Plane) ∈ Metric.sphere 0 1}

theorem actual_band_rejects_internal_disk
    {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (B : CompatibleOutsideBands D) {c : Curve S}
    (hfront : frontier
      (Set.range D.square ∪ Set.range B.first ∪ Set.range B.second) = c.image)
    (f : C(UnitDisk, S)) (hf : IsEmbedding f)
    (hboundary : f '' diskBoundary = c.image)
    (hinside : f '' diskInterior ⊆ interior
      (Set.range D.square ∪ Set.range B.first ∪ Set.range B.second)) : False := by
  exact CapBandGeometry.actual_band_internal_disk_false D B hfront f hf hboundary hinside

#print axioms actual_band_rejects_internal_disk
end CurveComplex
