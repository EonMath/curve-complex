import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualDevelopmentFamilyProbe
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualBranchContractiveDevelopmentCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualDevelopmentBallRestrictionCandidate

namespace CurveComplex.Hyperbolic
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S] [T1Space S]

theorem actual_branch_development_family_coverage (q : BranchedDoubleCover E S)
    (identify : S ≃ₜ Metric.GlueSpace (boundaryInclusion_isometry regularHexagonRegion)
      (boundaryInclusion_isometry regularHexagonRegion))
    (x : E) (hx : x ∈ q.ramification) (i : Fin 6)
    (hposition : identify (q.projection x) = Metric.toGlueL
      (boundaryInclusion_isometry regularHexagonRegion)
      (boundaryInclusion_isometry regularHexagonRegion)
      ⟨regularHexagonCandidate.vertex i,
        hexagon_vertex_mem_closure regularHexagonCandidate regularHexagonRegion i⟩) :
    ∃ f ∈ actualCompactDevelopmentFamily q identify, x ∈ f.source := by
  obtain ⟨e, d, hxe, hcenter, hprojection, hdeck, hpunctured, hcontract⟩ :=
    actual_branch_contractive_development q identify x hx i hposition
  obtain ⟨f, hxf, hfe, r, hr, htarget, hvalue, hfcontract⟩ :=
    contractive_development_ball_restriction (fun y => identify (q.projection y)) e x hxe hcontract
  refine ⟨f, ?_, hxf⟩
  exact ⟨e x, r, hr, htarget, hfcontract⟩

end CurveComplex.Hyperbolic
