import CurveComplexGenusTwo.Topology.ThetaRetention.ActualSourceSurgeryBranches

namespace CurveComplex

/-- Actual source surgery inputs for a specified pair of nonseparating
vertices. Every representative, path and embedded boundary is constructed;
this structure contains no assumed new nonseparating vertex or assumed
intersection-decreasing surgery. -/
structure SourceNonseparatingSurgeryPreparation
    (S : Type) [TopologicalSpace S]
    (α β : {v : Vertex S // nonseparatingVertex v}) where
  current : EssentialCurve S
  target : EssentialCurve S
  current_class : Quotient.mk (essentialCurveSetoid S) current = α.val
  target_class : Quotient.mk (essentialCurveSetoid S) target = β.val
  current_nonseparating : Nonseparating current.val
  target_nonseparating : Nonseparating target.val
  transverse : Transverse current.val target.val
  minimum_count : transverse.1.toFinset.card = geometricIntersection α.val β.val
  first_return : SourceFirstReturnBoundary target.val current.val
  branches : SourceTwoSurgeryBranches first_return
  crossing_budget : ∀ i : Bool,
    let R := (Set.range (branches.closing i) ∩ target.val.image) \
      {first_return.start,first_return.finish}
    R.Finite ∧ R.ncard + 2 ≤ geometricIntersection α.val β.val

/-- The complete concrete starting package for intersection-reducing source
surgery is produced for every actual nonseparating pair above the edge bound. -/
theorem source_nonseparating_surgery_preparation
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (α β : {v : Vertex S // nonseparatingVertex v})
    (hlarge : 1 < geometricIntersection α.val β.val) :
    Nonempty (SourceNonseparatingSurgeryPreparation S α β) := by
  obtain ⟨a,b,ha,hb,hna,hnb,ht,hmin,⟨D⟩⟩ :=
    source_nonseparating_minimal_first_return S α β hlarge
  obtain ⟨B⟩ := source_first_return_two_surgery_branches D
  have hcount : (b.val.image ∩ a.val.image).ncard =
      geometricIntersection α.val β.val := by
    rw [Set.inter_comm,Set.ncard_eq_toFinset_card _ ht.1]
    exact hmin
  refine ⟨{
    current := a, target := b, current_class := ha, target_class := hb,
    current_nonseparating := hna, target_nonseparating := hnb,
    transverse := ht, minimum_count := hmin,
    first_return := D, branches := B, crossing_budget := ?_ }⟩
  intro i
  have hbudget := source_surgery_closing_crossings_budget D B
    (transverse_symm_of_chart ht) i
  simpa only [hcount] using hbudget

/-- For arbitrary actual nonseparating source vertices, either their genuine
realization edge is constructed, or both actual raw surgery branches and
strict retained-crossing budgets are constructed. This is a produced case
split, not a connectivity conclusion. -/
theorem source_nonseparating_edge_or_surgery_preparation
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (α β : {v : Vertex S // nonseparatingVertex v}) :
    Nonempty (Path
      (CurveComplexGenusTwo.SourceTopology.nonseparatingVertexPoint S α)
      (CurveComplexGenusTwo.SourceTopology.nonseparatingVertexPoint S β)) ∨
    Nonempty (SourceNonseparatingSurgeryPreparation S α β) := by
  by_cases h : geometricIntersection α.val β.val ≤ 1
  · exact Or.inl ⟨CurveComplexGenusTwo.SourceTopology.actual_nonseparating_edge_path S α β h⟩
  · exact Or.inr (source_nonseparating_surgery_preparation S α β (Nat.lt_of_not_ge h))

/-- This concrete case split uses exactly the surface assumptions of the
original genus-two endpoint, deriving the closed-surface instances from IsGenus. -/
theorem source_genus_two_nonseparating_edge_or_surgery_preparation
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (hS : IsGenus S 2)
    (α β : {v : Vertex S // nonseparatingVertex v}) :
    Nonempty (Path
      (CurveComplexGenusTwo.SourceTopology.nonseparatingVertexPoint S α)
      (CurveComplexGenusTwo.SourceTopology.nonseparatingVertexPoint S β)) ∨
    Nonempty (SourceNonseparatingSurgeryPreparation S α β) := by
  let : ClosedSurface S := Classical.choice hS.2.1
  exact source_nonseparating_edge_or_surgery_preparation S α β

end CurveComplex

#print axioms CurveComplex.source_nonseparating_surgery_preparation
#print axioms CurveComplex.source_nonseparating_edge_or_surgery_preparation

#print axioms CurveComplex.source_genus_two_nonseparating_edge_or_surgery_preparation
