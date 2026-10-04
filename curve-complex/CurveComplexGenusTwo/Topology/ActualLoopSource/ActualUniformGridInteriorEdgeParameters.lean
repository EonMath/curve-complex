import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualOuterGridEdgeLiteralMovies
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- The actual interior grid node is literally the initial endpoint of its
incident upper/right cell's affine parameter. -/
theorem actual_uniform_mesh_node_as_cell_start (n : ℕ) (hn : 0<n) (j : Fin n) :
    actualHalfMeshParameter n hn ⟨2*j.val,by omega⟩=
      ArcFinitePosition.intervalMeshParameter n hn j 0 := by
  apply Subtype.ext
  change ((2*j.val:ℕ):ℝ)/(2*n)=((j.val:ℝ)+0)/n
  have hnR : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  push_cast
  field_simp
  ring
/-- Converting an interior horizontal physical edge into its original upper
cell indexing preserves every literal parameter. -/
theorem actual_uniform_grid_horizontal_interior_parameter
    (n : ℕ) (hn : 0<n) (e : Fin n × Fin n) (t : Interval) :
    actualUniformGridEdgeParameter n hn (Sum.inl (e.1,e.2.castSucc)) t=
      (ArcFinitePosition.intervalMeshParameter n hn e.1 t,
        ArcFinitePosition.intervalMeshParameter n hn e.2 0) := by
  change (_,actualHalfMeshParameter n hn ⟨2*e.2.val,by omega⟩)=_
  rw [actual_uniform_mesh_node_as_cell_start]
/-- The analogous vertical physical edge retains its original right-cell
parameterization. -/
theorem actual_uniform_grid_vertical_interior_parameter
    (n : ℕ) (hn : 0<n) (e : Fin n × Fin n) (t : Interval) :
    actualUniformGridEdgeParameter n hn (Sum.inr (e.1.castSucc,e.2)) t=
      (ArcFinitePosition.intervalMeshParameter n hn e.1 0,
        ArcFinitePosition.intervalMeshParameter n hn e.2 t) := by
  change (actualHalfMeshParameter n hn ⟨2*e.1.val,by omega⟩,_)=_
  rw [actual_uniform_mesh_node_as_cell_start]
end CurveComplex.HyperellipticModel
