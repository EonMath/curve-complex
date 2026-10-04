import CurveComplexGenusTwo.Dictionary.ArcVertexAPI
import CurveComplexGenusTwo.Dictionary.Projection.InvariantCurveFixedProjectsArc

open Set Topology

namespace CurveComplex.HyperellipticModel

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
  (M : HyperellipticModel E S)

/--
The branch-meeting half of the invariant-curve dictionary classification.
This is a direct exact-header wrapper around the existing actual projection
producer, with no extra geometric premise beyond the branch-hit witness.
-/
theorem invariant_essential_curve_projects_nonloop_arc_of_branch
    (c : EssentialCurve E)
    (hc : M.cover.deck '' c.val.image = c.val.image)
    (hbranch : ∃ t, M.cover.projection (c.val.map t) ∈ M.cover.branch) :
    (∃ a : NonLoopArc M, c.val.image = M.cover.projection ⁻¹' a.image) := by
  exact M.invariant_curve_meeting_branch_projects_nonloop_arc c.val hc hbranch

/--
The same branch-meeting case embedded in the full source disjunction.
-/
theorem invariant_essential_curve_projects_dictionary_of_branch
    (c : EssentialCurve E)
    (hc : M.cover.deck '' c.val.image = c.val.image)
    (hbranch : ∃ t, M.cover.projection (c.val.map t) ∈ M.cover.branch) :
    (∃ a : NonLoopArc M, c.val.image = M.cover.projection ⁻¹' a.image) ∨
      (∃ a : Circle33 M, c.val.image = M.cover.projection ⁻¹' a.val.image) := by
  exact Or.inl (M.invariant_essential_curve_projects_nonloop_arc_of_branch c hc hbranch)

#print axioms CurveComplex.HyperellipticModel.invariant_essential_curve_projects_nonloop_arc_of_branch
#print axioms CurveComplex.HyperellipticModel.invariant_essential_curve_projects_dictionary_of_branch

end CurveComplex.HyperellipticModel
