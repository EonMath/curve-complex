import ClassificationSchoenflies.PlanarDiskProducer
import ClassificationSchoenflies.TopologicalDiskBoundaryExtension

open Set Metric
open LeanEval.Topology.ClassificationOfSurfaces.Moise

namespace ClassificationSchoenflies

/-- The planar enclosure carries all data needed for the marked-sphere disk:
an actual closed-disk homeomorphism and an embedded parametrization of its
entire frontier by the source's complex unit circle. -/
theorem exists_polygonalDisk_certificate
    {A : Set Plane} (hAcompact : IsCompact A) (hAconnected : IsConnected A)
    (hComp : IsConnected Aᶜ)
    (F : Finset Plane) (hF : ∀ x ∈ F, x ∉ A) :
    ∃ Q : PolygonalCircle,
      A ⊆ interior Q.closedRegion ∧
      Disjoint Q.closedRegion (F : Set Plane) ∧
      Nonempty (closedBall (0 : Plane) 1 ≃ₜ Q.closedRegion) ∧
      ∃ boundaryMap : Circle → Plane,
        Topology.IsEmbedding boundaryMap ∧
        range boundaryMap = frontier Q.closedRegion := by
  obtain ⟨Q, hAinside, hAvoid⟩ :=
    exists_polygonalDisk_avoiding_finite hAcompact hAconnected hComp F hF
  let J : JordanCircle := Q.toJordanCircle
  let boundaryMap : Circle → Plane :=
    J.parametrization ∘ PlaneAlexander.sphereToCircle.symm
  have hJembed : Topology.IsEmbedding J.parametrization :=
    (J.continuous.isClosedEmbedding J.injective).isEmbedding
  have hBoundaryEmbed : Topology.IsEmbedding boundaryMap :=
    hJembed.comp PlaneAlexander.sphereToCircle.symm.isEmbedding
  have hBoundaryRange : range boundaryMap = frontier Q.closedRegion := by
    change range (J.parametrization ∘ PlaneAlexander.sphereToCircle.symm) =
      frontier Q.closedRegion
    rw [Set.range_comp, PlaneAlexander.sphereToCircle.symm.surjective.range_eq,
      Set.image_univ]
    change J.carrier = frontier Q.closedRegion
    rw [Q.carrier_toJordanCircle, Q.frontier_closedRegion]
  exact ⟨Q, hAinside, hAvoid, ⟨(PolygonalCircle.closedRegionToBall Q).symm⟩,
    boundaryMap, hBoundaryEmbed, hBoundaryRange⟩

/-- An embedded planar interval admits a polygonal disk certificate avoiding
any finite set of off-arc marks.  The complement connectivity follows from
the proved planar arc nonseparation theorem. -/
theorem exists_polygonalDisk_certificate_for_arc
    (g : unitInterval → Plane) (hgCont : Continuous g)
    (hgInj : Function.Injective g)
    (F : Finset Plane) (hF : ∀ x ∈ F, x ∉ range g) :
    ∃ Q : PolygonalCircle,
      range g ⊆ interior Q.closedRegion ∧
      Disjoint Q.closedRegion (F : Set Plane) ∧
      Nonempty (closedBall (0 : Plane) 1 ≃ₜ Q.closedRegion) ∧
      ∃ boundaryMap : Circle → Plane,
        Topology.IsEmbedding boundaryMap ∧
        range boundaryMap = frontier Q.closedRegion := by
  have hEmbedding : Topology.IsEmbedding g :=
    (hgCont.isClosedEmbedding hgInj).isEmbedding
  have hComp : IsConnected (range g)ᶜ :=
    ClassificationJordanCurve.arc_not_separates ClassificationJordanCurve.Brouwer.brouwerFPT
      hEmbedding.toHomeomorph.symm
  exact exists_polygonalDisk_certificate (isCompact_range hgCont)
    (isConnected_range hgCont) hComp F hF

end ClassificationSchoenflies
