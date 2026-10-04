import CurveComplexGenusTwo.Dictionary.ActualTwoMarkClosedSide
import CurveComplexGenusTwo.Dictionary.EssentialPreimageMarkedSidesAtLeastTwo
import CurveComplexGenusTwo.Dictionary.BranchClassification
import CurveComplexGenusTwo.Dictionary.Projection.InvariantCurveFreeProjectsCircle

namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- The actual essential preimage forces the two punctured-circle sides to
contain three branch points each. -/
theorem essential_preimage_splits_three_three
    (M : HyperellipticModel E S) (a : PuncturedCircle M)
    (c : EssentialCurve E)
    (hc : c.val.image = M.cover.projection ⁻¹' a.image) :
    SplitsMarked M a 3 3 := by
  obtain ⟨m,n,hm,hn,hsum,hsplit⟩ := M.essentialPreimage_markedSidesAtLeastTwo a c hc
  obtain ⟨hm2,hn2⟩ := M.full_preimage_curve_splits_no_two a c.val hc m n hsplit
  have hm3 : m = 3 := by omega
  have hn3 : n = 3 := by omega
  simpa only [hm3,hn3] using hsplit

/-- Source Lemma 4.4: an actual invariant essential curve projects to one of the dictionary types. -/
theorem invariant_essential_curve_projects_dictionary (M : HyperellipticModel E S)
    (c : EssentialCurve E)
    (hc : M.cover.deck '' c.val.image = c.val.image) :
    (∃ a : NonLoopArc M, c.val.image = M.cover.projection ⁻¹' a.image) ∨
    (∃ a : Circle33 M, c.val.image = M.cover.projection ⁻¹' a.val.image) := by
  classical
  by_cases hbranch : ∃ t, M.cover.projection (c.val.map t) ∈ M.cover.branch
  · exact M.invariant_essential_curve_projects_dictionary_of_branch c hc hbranch
  · have havoid : ∀ t, M.cover.projection (c.val.map t) ∉ M.cover.branch := by
      simpa only [not_exists] using hbranch
    obtain ⟨a,ha,_⟩ := M.invariant_curve_avoiding_branch_projects_punctured_circle c.val hc havoid
    exact Or.inr ⟨⟨a,M.essential_preimage_splits_three_three a c ha⟩,ha⟩

#print axioms CurveComplex.HyperellipticModel.essential_preimage_splits_three_three
#print axioms CurveComplex.HyperellipticModel.invariant_essential_curve_projects_dictionary
end CurveComplex.HyperellipticModel
