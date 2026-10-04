import CurveComplexGenusTwo.Topology.ActualConnectivity.CanonicalGlobalNonseparatingPointPaths
namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex
theorem source_genus_two_nonseparating_points_joined
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (hS : IsGenus S 2)
    (x y : NonseparatingLocus S) : Joined x y := by
  let e := nonseparatingRealizationHomeomorph S
  obtain ⟨p⟩ := actual_genus_two_nonseparating_points_joined S hS (e.symm x) (e.symm y)
  exact ⟨(p.map e.continuous).cast (e.apply_symm_apply x).symm (e.apply_symm_apply y).symm⟩
end CurveComplexGenusTwo.SourceTopology
#print axioms CurveComplexGenusTwo.SourceTopology.source_genus_two_nonseparating_points_joined
