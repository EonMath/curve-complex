import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualLiteralCellSides
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Each literal outer physical edge is the corresponding side of an actual
uniform cell, including the n=1 mesh and all original corners. -/
theorem actual_outer_grid_cell_side (n : ℕ) (hn : 0<n) (i : Fin n) (side : Fin 4) :
    ∃ k : Fin n × Fin n,
      actualUniformCellGridSide n k side=actualUniformOuterGridEdge n i side := by
  let first : Fin n := ⟨0,hn⟩
  let last : Fin n := ⟨n-1,by omega⟩
  fin_cases side
  · exact ⟨(i,first),by simp [actualUniformCellGridSide,actualUniformOuterGridEdge,first]⟩
  · refine ⟨(last,i),?_⟩
    simp [actualUniformCellGridSide,actualUniformOuterGridEdge,last,Fin.ext_iff]
    omega
  · refine ⟨(i,last),?_⟩
    simp [actualUniformCellGridSide,actualUniformOuterGridEdge,last,Fin.ext_iff]
    omega
  · exact ⟨(first,i),by simp [actualUniformCellGridSide,actualUniformOuterGridEdge,first]⟩
theorem actual_literal_cell_side_boundary (side : Fin 4) (t : Interval) :
    (actualLiteralCellSide side t).1=0 ∨ (actualLiteralCellSide side t).1=1 ∨
      (actualLiteralCellSide side t).2=0 ∨ (actualLiteralCellSide side t).2=1 := by
  fin_cases side <;> simp [actualLiteralCellSide]
end CurveComplex.HyperellipticModel
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- The actual literal outer physical edges cover the complete original square
boundary; endpoint parameters retain the original corners. -/
theorem actual_outer_grid_boundary_cover (n : ℕ) (hn : 0<n)
    (z : Interval × Interval) (hz : z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1) :
    ∃ side : Fin 4,∃ i : Fin n,∃ t : Interval,
      actualUniformGridEdgeParameter n hn (actualUniformOuterGridEdge n i side) t=z := by
  rcases hz with h | h | h | h
  · obtain ⟨i,t,ht⟩ := ArcFinitePosition.intervalMeshParameter_cover n hn z.2
    refine ⟨3,i,t,?_⟩
    rw [actual_outer_grid_edge_literal_values]
    norm_num
    exact Prod.ext h.symm ht
  · obtain ⟨i,t,ht⟩ := ArcFinitePosition.intervalMeshParameter_cover n hn z.2
    refine ⟨1,i,t,?_⟩
    rw [actual_outer_grid_edge_literal_values]
    norm_num
    exact Prod.ext h.symm ht
  · obtain ⟨i,t,ht⟩ := ArcFinitePosition.intervalMeshParameter_cover n hn z.1
    refine ⟨0,i,t,?_⟩
    rw [actual_outer_grid_edge_literal_values]
    norm_num
    exact Prod.ext ht h.symm
  · obtain ⟨i,t,ht⟩ := ArcFinitePosition.intervalMeshParameter_cover n hn z.1
    refine ⟨2,i,t,?_⟩
    rw [actual_outer_grid_edge_literal_values]
    norm_num
    exact Prod.ext ht h.symm
end CurveComplex.HyperellipticModel
