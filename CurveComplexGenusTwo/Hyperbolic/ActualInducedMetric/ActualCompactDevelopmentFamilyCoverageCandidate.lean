import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualBranchDevelopmentFamilyCoverageCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualInteriorDevelopmentFamilyCoverageCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualRightInteriorDevelopmentFamilyCoverageCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualSeamDevelopmentFamilyCoverageCandidate

namespace CurveComplex.Hyperbolic
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S] [T1Space S]

theorem actual_compact_development_family_coverage (q : BranchedDoubleCover E S)
    (identify : S ≃ₜ Metric.GlueSpace (boundaryInclusion_isometry regularHexagonRegion)
      (boundaryInclusion_isometry regularHexagonRegion))
    (hmatch : ∀ b : S, b ∈ q.branch ↔ identify b ∈ Set.range
      (fun i : Fin 6 => Metric.toGlueL (boundaryInclusion_isometry regularHexagonRegion)
        (boundaryInclusion_isometry regularHexagonRegion)
        ⟨regularHexagonCandidate.vertex i,
          hexagon_vertex_mem_closure regularHexagonCandidate regularHexagonRegion i⟩)) :
    ∀ x : E, ∃ f ∈ actualCompactDevelopmentFamily q identify, x ∈ f.source := by
  intro x
  let R := regularHexagonRegion
  let L := Metric.toGlueL (boundaryInclusion_isometry R) (boundaryInclusion_isometry R)
  let Q := Metric.toGlueR (boundaryInclusion_isometry R) (boundaryInclusion_isometry R)
  by_cases hxram : x ∈ q.ramification
  · obtain ⟨i, hi⟩ := (hmatch (q.projection x)).mp hxram
    exact actual_branch_development_family_coverage q identify x hxram i hi.symm
  · have hno : identify (q.projection x) ∉ Set.range
        (fun i : Fin 6 => L ⟨regularHexagonCandidate.vertex i,
          hexagon_vertex_mem_closure regularHexagonCandidate R i⟩) := by
      intro hn
      exact hxram ((hmatch (q.projection x)).mpr hn)
    have hseam (c : ClosedPolygon R) (hc : (c : H2) ∈ frontier R.interior)
        (hpos : identify (q.projection x) = L c) :
        ∃ f ∈ actualCompactDevelopmentFamily q identify, x ∈ f.source := by
      have hnv (j : Fin 6) : (c : H2) ≠ regularHexagonCandidate.vertex j := by
        intro heq
        apply hno
        refine ⟨j, ?_⟩
        rw [hpos]
        apply congrArg L
        exact Subtype.ext heq.symm
      have hedges : (c : H2) ∈ ⋃ i : Fin 6, regularHexagonCandidate.edge i := by
        rwa [← R.boundary_is_edges]
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hedges
      exact actual_seam_development_family_coverage q identify x hxram c i hi (hnv i) (hnv (i+1)) hpos
    have hall : ∀ z : Metric.GlueSpace (boundaryInclusion_isometry R)
        (boundaryInclusion_isometry R), (∃ c, L c = z) ∨ ∃ c, Q c = z := by
      intro z
      refine Quotient.inductionOn z ?_
      intro v
      cases v with
      | inl c => exact Or.inl ⟨c, rfl⟩
      | inr c => exact Or.inr ⟨c, rfl⟩
    rcases hall (identify (q.projection x)) with ⟨c, hc⟩ | ⟨c, hc⟩
    · by_cases hci : (c : H2) ∈ R.interior
      · apply actual_left_interior_development_family_coverage q identify x hxram
        exact ⟨c, hci, hc⟩
      · have hfront : (c : H2) ∈ frontier R.interior := by
          by_contra hf
          exact hci ((closedPolygon_interior_iff_not_frontier R c).mpr hf)
        exact hseam c hfront hc.symm
    · by_cases hci : (c : H2) ∈ R.interior
      · apply actual_right_interior_development_family_coverage q identify x hxram
        exact ⟨c, hci, hc⟩
      · have hfront : (c : H2) ∈ frontier R.interior := by
          by_contra hf
          exact hci ((closedPolygon_interior_iff_not_frontier R c).mpr hf)
        have hlr : L c = Q c := (polygon_double_cross_copy_eq_iff R c c).mpr ⟨rfl, hfront⟩
        exact hseam c hfront (hc.symm.trans hlr.symm)

end CurveComplex.Hyperbolic
