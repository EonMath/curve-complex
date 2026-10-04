import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches
import CurveComplexGenusTwo.Topology.GlobalMonodromy.GlobalLoopSubdivision

open CurveComplex Set Topology

theorem regional_actualSubpath_range_of_le
    {X : Type} [TopologicalSpace X] {x y : X}
    (γ : Path x y) (l r : Interval) (hlr : l ≤ r) :
    Set.range (CurveComplex.BranchedDoubleCover.actualSubpath γ l r) =
      γ '' Set.Icc l r := by
  change Set.range (γ.subpath l r) = γ '' Set.Icc l r
  exact Path.range_subpath_of_le γ l r hlr

#print axioms regional_actualSubpath_range_of_le
