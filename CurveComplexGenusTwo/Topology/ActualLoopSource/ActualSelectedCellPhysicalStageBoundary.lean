import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSelectedCellGenuineSurfaceMovie
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Every literal cell-boundary point has its actual side parameter. -/
theorem actual_literal_cell_boundary_parameter (z : Interval × Interval)
    (hz : z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1) :
    ∃ side : Fin 4,∃ t : Interval,actualLiteralCellSide side t=z := by
  rcases hz with h | h | h | h
  · exact ⟨3,z.2,by simp only [actualLiteralCellSide]; exact Prod.ext h.symm rfl⟩
  · exact ⟨1,z.2,by simp only [actualLiteralCellSide]; exact Prod.ext h.symm rfl⟩
  · exact ⟨0,z.1,by simp only [actualLiteralCellSide]; exact Prod.ext rfl h.symm⟩
  · exact ⟨2,z.1,by simp only [actualLiteralCellSide]; exact Prod.ext rfl h.symm⟩
/-- The actual lifted stages use the produced physical assignment at every
boundary point, including corners. Their bridge values follow from stage
endpoints, so no new compatibility or geometry hypothesis is introduced. -/
theorem actual_selected_cell_physical_stage_boundary
    {S : Type} [TopologicalSpace S]
    (n : ℕ) (hn : 0<n) (k : Fin n × Fin n)
    (f0 f1 f2 f3 : C(Interval × Interval,S))
    (first : f0.Homotopy f1) (middle : f1.Homotopy f2) (last : f2.Homotopy f3)
    (movie : ((Fin n × Fin (n+1)) ⊕ (Fin (n+1) × Fin n)) → C(Interval × Interval,S))
    (B : ((Interval × Interval) × Interval) → S)
    (hB : ∀ e t σ,B (actualUniformGridEdgeParameter n hn e t,σ)=movie e (σ,t))
    (hmiddle : ∀ side σ t,middle (σ,actualLiteralCellSide side t)=
      movie (actualUniformCellGridSide n k side) (σ,t))
    (hfirst : ∀ σ z,z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 → first (σ,z)=f0 z)
    (hlast : ∀ σ z,z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 → last (σ,z)=f3 z) :
      (∀ z σ,z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 →
        first (σ,z)=B ((ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
          ArcFinitePosition.intervalMeshParameter n hn k.2 z.2),0)) ∧
      (∀ z σ,z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 →
        middle (σ,z)=B ((ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
          ArcFinitePosition.intervalMeshParameter n hn k.2 z.2),σ)) ∧
      (∀ z σ,z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 →
        last (σ,z)=B ((ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
          ArcFinitePosition.intervalMeshParameter n hn k.2 z.2),1)) := by
  have hmid (z : Interval × Interval) (σ : Interval)
      (hz : z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1) : middle (σ,z)=
      B ((ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
        ArcFinitePosition.intervalMeshParameter n hn k.2 z.2),σ) := by
    obtain ⟨side,t,rfl⟩ := actual_literal_cell_boundary_parameter z hz
    rw [actual_literal_cell_side_grid_parameter,hB]
    exact hmiddle side σ t
  refine ⟨?_,hmid,?_⟩
  · intro z σ hz
    calc
      first (σ,z)=f0 z := hfirst σ z hz
      _=first (1,z) := (hfirst 1 z hz).symm
      _=middle (0,z) := (first.map_one_left z).trans (middle.map_zero_left z).symm
      _=_ := hmid z 0 hz
  · intro z σ hz
    calc
      last (σ,z)=f3 z := hlast σ z hz
      _=last (0,z) := (hlast 0 z hz).symm
      _=middle (1,z) := (last.map_zero_left z).trans (middle.map_one_left z).symm
      _=_ := hmid z 1 hz
end CurveComplex.HyperellipticModel
