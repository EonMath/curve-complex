import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualUniformMeshFiniteContactRestriction
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualUniformGridSharedBoundaryAssignment
namespace CurveComplex.HyperellipticModel
open Set Topology
noncomputable def actualUniformOuterGridEdge (n : ℕ) (i : Fin n) (side : Fin 4) :
    (Fin n × Fin (n+1)) ⊕ (Fin (n+1) × Fin n) :=
  if side.val=0 then Sum.inl (i,0)
  else if side.val=1 then Sum.inr (⟨n,Nat.lt_succ_self n⟩,i)
  else if side.val=2 then Sum.inl (i,⟨n,Nat.lt_succ_self n⟩)
  else Sum.inr (0,i)
theorem actual_outer_grid_edge_literal_values (n : ℕ) (hn : 0<n)
    (i : Fin n) (side : Fin 4) (t : Interval) :
    actualUniformGridEdgeParameter n hn (actualUniformOuterGridEdge n i side) t=
      if side.val=0 then (ArcFinitePosition.intervalMeshParameter n hn i t,0)
      else if side.val=1 then (1,ArcFinitePosition.intervalMeshParameter n hn i t)
      else if side.val=2 then (ArcFinitePosition.intervalMeshParameter n hn i t,1)
      else (0,ArcFinitePosition.intervalMeshParameter n hn i t) := by
  fin_cases side <;> simp [actualUniformOuterGridEdge,actualUniformGridEdgeParameter,
    actual_uniform_mesh_node_last]
  all_goals
    apply Subtype.ext
    simp [actualHalfMeshParameter]
/-- The four literal outer-side edge families are constructed as constant movies
of the original boundary, with finite final contacts proved by injective mesh
restriction. All original corners remain literal. -/
theorem actual_outer_grid_edge_literal_movies
    {Y : Type} [TopologicalSpace Y] (old forbidden : Set Y)
    (F : C(Interval × Interval,Y)) (hmarks : ∀ z,F z ∉ forbidden)
    (hbottom : {t : Interval | F (t,0) ∈ old}.Finite)
    (hright : {t : Interval | F (1,t) ∈ old}.Finite)
    (htop : {t : Interval | F (t,1) ∈ old}.Finite)
    (hleft : {t : Interval | F (0,t) ∈ old}.Finite)
    (n : ℕ) (hn : 0<n) :
    ∃ movie : Fin 4 → Fin n → C(Interval × Interval,Y),
      (∀ side i σ t,movie side i (σ,t)=
        F (actualUniformGridEdgeParameter n hn (actualUniformOuterGridEdge n i side) t)) ∧
      (∀ side i z,movie side i z ∉ forbidden) ∧
      (∀ side i,{t : Interval | movie side i (1,t) ∈ old}.Finite) := by
  let movie : Fin 4 → Fin n → C(Interval × Interval,Y) := fun side i =>
    ⟨fun z => F (actualUniformGridEdgeParameter n hn (actualUniformOuterGridEdge n i side) z.2),
      F.continuous.comp ((actualUniformGridEdgeParameter n hn
        (actualUniformOuterGridEdge n i side)).continuous.comp continuous_snd)⟩
  refine ⟨movie,(fun _ _ _ _ => rfl),(fun _ _ z => hmarks _),?_⟩
  intro side i
  let bottom : C(Interval,Y) := ⟨fun t => F (t,0),by fun_prop⟩
  let right : C(Interval,Y) := ⟨fun t => F (1,t),by fun_prop⟩
  let top : C(Interval,Y) := ⟨fun t => F (t,1),by fun_prop⟩
  let left : C(Interval,Y) := ⟨fun t => F (0,t),by fun_prop⟩
  fin_cases side
  · simpa [movie,actual_outer_grid_edge_literal_values,bottom] using
      actual_uniform_mesh_finite_contact_restriction old bottom hbottom n hn i
  · simpa [movie,actual_outer_grid_edge_literal_values,right] using
      actual_uniform_mesh_finite_contact_restriction old right hright n hn i
  · simpa [movie,actual_outer_grid_edge_literal_values,top] using
      actual_uniform_mesh_finite_contact_restriction old top htop n hn i
  · simpa [movie,actual_outer_grid_edge_literal_values,left] using
      actual_uniform_mesh_finite_contact_restriction old left hleft n hn i
end CurveComplex.HyperellipticModel
