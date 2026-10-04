import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualPreparedLoopWholeGridEdgeMoviesInRange
namespace CurveComplex.HyperellipticModel
open Set Topology
theorem actual_uniform_mesh_node_as_cell_end (n : ℕ) (hn : 0<n) (j : Fin n) :
    actualHalfMeshParameter n hn ⟨2*j.succ.val,by omega⟩=
      ArcFinitePosition.intervalMeshParameter n hn j 1 := by
  apply Subtype.ext
  change ((2*(j.val+1):ℕ):ℝ)/(2*n)=((j.val:ℝ)+1)/n
  have hnR : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  push_cast
  field_simp
noncomputable def actualUniformCellGridSide (n : ℕ) (k : Fin n × Fin n) (side : Fin 4) :
    (Fin n × Fin (n+1)) ⊕ (Fin (n+1) × Fin n) :=
  if side.val=0 then Sum.inl (k.1,k.2.castSucc)
  else if side.val=1 then Sum.inr (k.1.succ,k.2)
  else if side.val=2 then Sum.inl (k.1,k.2.succ)
  else Sum.inr (k.1.castSucc,k.2)
/-- Every cell side uses the literal physical grid edge, with the SAME side
parameter as the joint cone filling. -/
theorem actual_uniform_cell_physical_grid_side_parameter
    (n : ℕ) (hn : 0<n) (k : Fin n × Fin n) (side : Fin 4) (t : Interval) :
    actualUniformGridEdgeParameter n hn (actualUniformCellGridSide n k side) t=
      if side.val=0 then
        (ArcFinitePosition.intervalMeshParameter n hn k.1 t,ArcFinitePosition.intervalMeshParameter n hn k.2 0)
      else if side.val=1 then
        (ArcFinitePosition.intervalMeshParameter n hn k.1 1,ArcFinitePosition.intervalMeshParameter n hn k.2 t)
      else if side.val=2 then
        (ArcFinitePosition.intervalMeshParameter n hn k.1 t,ArcFinitePosition.intervalMeshParameter n hn k.2 1)
      else
        (ArcFinitePosition.intervalMeshParameter n hn k.1 0,ArcFinitePosition.intervalMeshParameter n hn k.2 t) := by
  fin_cases side
  · change (_,actualHalfMeshParameter n hn ⟨2*k.2.val,by omega⟩)=_
    rw [actual_uniform_mesh_node_as_cell_start]
    norm_num
  · change (actualHalfMeshParameter n hn ⟨2*k.1.succ.val,by omega⟩,_)=_
    rw [actual_uniform_mesh_node_as_cell_end]
    norm_num
  · change (_,actualHalfMeshParameter n hn ⟨2*k.2.succ.val,by omega⟩)=_
    rw [actual_uniform_mesh_node_as_cell_end]
    norm_num
  · change (actualHalfMeshParameter n hn ⟨2*k.1.val,by omega⟩,_)=_
    rw [actual_uniform_mesh_node_as_cell_start]
    norm_num
/-- The complete literal physical edge belongs to its actual original cell. -/
theorem actual_uniform_cell_physical_grid_side_mem
    (n : ℕ) (hn : 0<n) (cell : (Fin n × Fin n) → Set (Interval × Interval))
    (hcell : ∀ k,cell k=range (fun z : Interval × Interval =>
      (ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
        ArcFinitePosition.intervalMeshParameter n hn k.2 z.2)))
    (k : Fin n × Fin n) (side : Fin 4) (t : Interval) :
    actualUniformGridEdgeParameter n hn (actualUniformCellGridSide n k side) t ∈ cell k := by
  rw [hcell k,actual_uniform_cell_physical_grid_side_parameter]
  fin_cases side
  · exact ⟨(t,0),rfl⟩
  · exact ⟨(1,t),rfl⟩
  · exact ⟨(t,1),rfl⟩
  · exact ⟨(0,t),rfl⟩
end CurveComplex.HyperellipticModel
