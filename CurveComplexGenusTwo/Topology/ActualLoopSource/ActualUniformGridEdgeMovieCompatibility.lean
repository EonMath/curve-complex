import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualUniformGridEdgeParameterGeometry
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Literal parameterization of every physical horizontal and vertical uniform
grid edge, including the outer boundary edges. -/
noncomputable def actualUniformGridEdgeParameter (n : ℕ) (hn : 0<n)
    (e : (Fin n × Fin (n+1)) ⊕ (Fin (n+1) × Fin n)) :
    C(Interval,Interval × Interval) := by
  cases e with
  | inl e => exact
      ⟨fun t => (ArcFinitePosition.intervalMeshParameter n hn e.1 t,
        actualHalfMeshParameter n hn ⟨2*e.2.val,by omega⟩),
        (ArcFinitePosition.intervalMeshParameter_continuous n hn e.1).prodMk continuous_const⟩
  | inr e => exact
      ⟨fun t => (actualHalfMeshParameter n hn ⟨2*e.1.val,by omega⟩,
        ArcFinitePosition.intervalMeshParameter n hn e.2 t),
        continuous_const.prodMk (ArcFinitePosition.intervalMeshParameter_continuous n hn e.2)⟩
/-- Actual endpoint-fixed grid-edge movies agree at every physical intersection.
This follows from the affine grid geometry; no overlap callback is supplied. -/
theorem actual_uniform_grid_edge_movie_compatibility
    {Y : Type} [TopologicalSpace Y] (F : C(Interval × Interval,Y))
    (n : ℕ) (hn : 0<n)
    (movie : ((Fin n × Fin (n+1)) ⊕ (Fin (n+1) × Fin n)) →
      C(Interval × Interval,Y))
    (hends : ∀ e σ t,t=0 ∨ t=1 → movie e (σ,t)=F (actualUniformGridEdgeParameter n hn e t))
    (e f : (Fin n × Fin (n+1)) ⊕ (Fin (n+1) × Fin n)) (t u : Interval)
    (he : actualUniformGridEdgeParameter n hn e t=actualUniformGridEdgeParameter n hn f u) :
    ∀ σ,movie e (σ,t)=movie f (σ,u) := by
  have hdone (ht : t=0 ∨ t=1) (hu : u=0 ∨ u=1) (σ : Interval) :
      movie e (σ,t)=movie f (σ,u) := by
    rw [hends e σ t ht,hends f σ u hu,he]
  cases e with
  | inl e =>
    cases f with
    | inl f =>
      have hnode := actual_uniform_mesh_node_injective n hn (congrArg Prod.snd he)
      have hmesh := actual_uniform_mesh_interval_collision n hn e.1 f.1 t u (congrArg Prod.fst he)
      rcases hmesh with ⟨hindex,htu⟩ | ⟨ht,hu⟩
      · have hef : e=f := Prod.ext hindex hnode
        subst f
        subst u
        exact fun _ => rfl
      · exact hdone ht hu
    | inr f =>
      have ht := actual_uniform_mesh_node_edge_endpoint n hn e.1 f.1 t (congrArg Prod.fst he)
      have hu := actual_uniform_mesh_node_edge_endpoint n hn f.2 e.2 u (congrArg Prod.snd he).symm
      exact hdone ht hu
  | inr e =>
    cases f with
    | inl f =>
      have ht := actual_uniform_mesh_node_edge_endpoint n hn e.2 f.2 t (congrArg Prod.snd he)
      have hu := actual_uniform_mesh_node_edge_endpoint n hn f.1 e.1 u (congrArg Prod.fst he).symm
      exact hdone ht hu
    | inr f =>
      have hnode := actual_uniform_mesh_node_injective n hn (congrArg Prod.fst he)
      have hmesh := actual_uniform_mesh_interval_collision n hn e.2 f.2 t u (congrArg Prod.snd he)
      rcases hmesh with ⟨hindex,htu⟩ | ⟨ht,hu⟩
      · have hef : e=f := Prod.ext hnode hindex
        subst f
        subst u
        exact fun _ => rfl
      · exact hdone ht hu
end CurveComplex.HyperellipticModel
