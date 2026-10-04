import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualCommonStripSurfaceCoordinates
namespace CurveComplex.HyperellipticModel
open Set Topology
noncomputable def actualLiteralCellSide (side : Fin 4) : C(Interval,Interval × Interval) :=
  if side.val=0 then ⟨fun t => (t,0),by fun_prop⟩
  else if side.val=1 then ⟨fun t => (1,t),by fun_prop⟩
  else if side.val=2 then ⟨fun t => (t,1),by fun_prop⟩
  else ⟨fun t => (0,t),by fun_prop⟩
/-- Local cone side parameters and actual physical grid side parameters match
literally after the original cell affine embedding. -/
theorem actual_literal_cell_side_grid_parameter
    (n : ℕ) (hn : 0<n) (k : Fin n × Fin n) (side : Fin 4) (t : Interval) :
    (ArcFinitePosition.intervalMeshParameter n hn k.1 (actualLiteralCellSide side t).1,
      ArcFinitePosition.intervalMeshParameter n hn k.2 (actualLiteralCellSide side t).2)=
      actualUniformGridEdgeParameter n hn (actualUniformCellGridSide n k side) t := by
  rw [actual_uniform_cell_physical_grid_side_parameter]
  fin_cases side <;> simp [actualLiteralCellSide]
end CurveComplex.HyperellipticModel
