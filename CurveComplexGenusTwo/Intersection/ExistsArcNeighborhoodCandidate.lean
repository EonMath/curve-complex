import CurveComplexGenusTwo.Intersection.ClassificationPlanarArcBundle
import CurveComplexGenusTwo.Intersection.ChartedArcCertificateInput
import CurveComplexGenusTwo.Intersection.MarkedBarrier

namespace CurveComplex.HyperellipticModel

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Candidate proof of the source dictionary's regular neighborhood theorem,
using the classification port's polygonal disk certificate. -/
theorem exists_arcNeighborhood_complete
    {M : HyperellipticModel E S} (a : NonLoopArc M) :
    Nonempty (ArcNeighborhood a) := by
  obtain ⟨p, hpBranch, hpArc⟩ := a.exists_marked_puncture
  let g : Interval → Schoenflies.Plane := chartedArcMap a p hpArc
  let F : Finset Schoenflies.Plane := planeForbiddenMarks a p
  have hgCont : Continuous g := by
    exact a.chartedArcMap_continuous p hpArc
  have hgInj : Function.Injective g := by
    exact a.chartedArcMap_injective p hpArc
  have hF : ∀ x ∈ F, x ∉ Set.range g := by
    intro x hx
    exact a.planeForbiddenMarks_avoid_arc p hpArc x hx
  obtain ⟨Q, hArc, hAvoid, hDisk, boundaryMap, hBoundaryEmbedded,
    hBoundaryRange⟩ :=
    ClassificationSchoenflies.exists_polygonalDisk_certificate_for_arc
      g hgCont hgInj F hF
  let K : Set Schoenflies.Plane := Q.closedRegion
  have hKcompact : IsCompact K := Q.isCompact_closedRegion
  have hDisk' : Nonempty (Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ K) := by
    simpa [K] using hDisk
  exact a.arcNeighborhood_of_planar_disk_avoiding_marks p hpArc K hKcompact
    hDisk'.some (by simpa [g, K] using hArc)
    (by simpa [F, K] using hAvoid)
    boundaryMap hBoundaryEmbedded (by simpa [K] using hBoundaryRange)

end CurveComplex.HyperellipticModel
