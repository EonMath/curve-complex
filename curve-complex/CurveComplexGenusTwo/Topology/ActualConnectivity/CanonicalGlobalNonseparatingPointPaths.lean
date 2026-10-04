import CurveComplexGenusTwo.Topology.ActualConnectivity.CanonicalGlobalNonseparatingFiniteChain
namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex
theorem actual_genus_two_nonseparating_points_joined
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (hS : IsGenus S 2)
    (x y : RealizationPoint (nonseparatingComplex S)) : Joined x y := by
  obtain ⟨α,hx⟩ := actual_nonseparating_point_joined_vertex S x
  obtain ⟨β,hy⟩ := actual_nonseparating_point_joined_vertex S y
  obtain ⟨n,v,hv0,hvn,hv⟩ := source_genus_two_nonseparating_finite_edge_chain S hS α β
  have hp : Joined (nonseparatingVertexPoint S α) (nonseparatingVertexPoint S β) := by
    rw [← hv0,← hvn]
    exact ⟨actual_nonseparating_finite_edge_path S v n hv⟩
  exact hx.trans (hp.trans hy.symm)
end CurveComplexGenusTwo.SourceTopology
#print axioms CurveComplexGenusTwo.SourceTopology.actual_genus_two_nonseparating_points_joined
