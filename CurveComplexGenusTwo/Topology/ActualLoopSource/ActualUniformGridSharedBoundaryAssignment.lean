import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualUniformGridEdgeMovieCompatibility
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- The actual endpoint-fixed edge movies construct a single shared boundary
assignment on the square. No boundary assignment or edge-overlap certificate is
supplied; all physical edge values are retained simultaneously. -/
theorem actual_uniform_grid_shared_boundary_assignment
    {Y : Type} [TopologicalSpace Y] (F : C(Interval × Interval,Y))
    (n : ℕ) (hn : 0<n)
    (movie : ((Fin n × Fin (n+1)) ⊕ (Fin (n+1) × Fin n)) →
      C(Interval × Interval,Y))
    (hends : ∀ e σ t,t=0 ∨ t=1 → movie e (σ,t)=F (actualUniformGridEdgeParameter n hn e t)) :
    ∃ B : ((Interval × Interval) × Interval) → Y,
      (∀ e t σ,B (actualUniformGridEdgeParameter n hn e t,σ)=movie e (σ,t)) ∧
      (∀ z σ,(¬∃ e t,actualUniformGridEdgeParameter n hn e t=z) → B (z,σ)=F z) := by
  classical
  let onGrid (z : Interval × Interval) :=
    ∃ e t,actualUniformGridEdgeParameter n hn e t=z
  let B : ((Interval × Interval) × Interval) → Y := fun z =>
    if h : onGrid z.1 then
      movie (Classical.choose h) (z.2,Classical.choose (Classical.choose_spec h))
    else F z.1
  refine ⟨B,?_,?_⟩
  · intro e t σ
    have h : onGrid (actualUniformGridEdgeParameter n hn e t) := ⟨e,t,rfl⟩
    dsimp only [B]
    rw [dite_eq_left h]
    have he := Classical.choose_spec (Classical.choose_spec h)
    exact actual_uniform_grid_edge_movie_compatibility F n hn movie hends
      (Classical.choose h) e (Classical.choose (Classical.choose_spec h)) t he σ
  · intro z σ hz
    exact dite_eq_right hz
end CurveComplex.HyperellipticModel
