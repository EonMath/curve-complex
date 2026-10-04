import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualLiteralCellSides
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Actual selected cell and its four physical shared-edge movies produce
continuous bounded strip coordinates, with literal initial/end-point matching
and actual finite final normal contacts. No coordinate maps are supplied. -/
theorem actual_selected_cell_four_edge_coordinates
    {S : Type} [TopologicalSpace S]
    (BC : Interval × Icc (-1:ℝ) 1 → S) (hBC : IsEmbedding BC)
    (old : Set S) (haxis : ∀ z,BC z ∈ old ↔ z.2.val=0)
    (R : C((Interval × Interval) × Interval,S)) (n : ℕ) (hn : 0<n)
    (cell : (Fin n × Fin n) → Set (Interval × Interval))
    (hcell : ∀ k,cell k=range (fun z : Interval × Interval =>
      (ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
        ArcFinitePosition.intervalMeshParameter n hn k.2 z.2)))
    (label : (Fin n × Fin n) → Bool)
    (hrange : ∀ k,label k=true → ∀ z ∈ cell k,∀ σ,R (z,σ) ∈ range BC)
    (movie : ((Fin n × Fin (n+1)) ⊕ (Fin (n+1) × Fin n)) → C(Interval × Interval,S))
    (hstart : ∀ e t,movie e (0,t)=R (actualUniformGridEdgeParameter n hn e t,1))
    (hends : ∀ e σ t,t=0 ∨ t=1 → movie e (σ,t)=R (actualUniformGridEdgeParameter n hn e t,1))
    (hfinite : ∀ e,{t : Interval | movie e (1,t) ∈ old}.Finite)
    (hmovieRange : ∀ e,(∀ t,R (actualUniformGridEdgeParameter n hn e t,1) ∈ range BC) →
      ∀ z,movie e z ∈ range BC)
    (k : Fin n × Fin n) (htrue : label k=true) :
    ∃ original : C(Interval × Interval,Icc (0:ℝ) 1 ×ˢ Icc (-1:ℝ) 1),
    ∃ edges : Fin 4 → C(Interval × Interval,Icc (0:ℝ) 1 ×ˢ Icc (-1:ℝ) 1),
      (∀ z,BC (actualStripProductCoordinates.symm (original z))=
        R ((ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
          ArcFinitePosition.intervalMeshParameter n hn k.2 z.2),1)) ∧
      (∀ side z,BC (actualStripProductCoordinates.symm (edges side z))=
        movie (actualUniformCellGridSide n k side) z) ∧
      (∀ side t,edges side (0,t)=original (actualLiteralCellSide side t)) ∧
      (∀ side σ t,t=0 ∨ t=1 → edges side (σ,t)=original (actualLiteralCellSide side t)) ∧
      (∀ side,{t : Interval | (edges side (1,t)).val.2=0}.Finite) := by
  classical
  let O : C(Interval × Interval,S) :=
    ⟨fun z => R ((ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
      ArcFinitePosition.intervalMeshParameter n hn k.2 z.2),1),by
      exact R.continuous.comp
        ((((ArcFinitePosition.intervalMeshParameter_continuous n hn k.1).comp continuous_fst).prodMk
          ((ArcFinitePosition.intervalMeshParameter_continuous n hn k.2).comp continuous_snd)).prodMk
            continuous_const)⟩
  have hO (z) : O z ∈ range BC := by
    apply hrange k htrue _ _ 1
    rw [hcell k]
    exact mem_range_self z
  obtain ⟨original,hOriginal⟩ := actual_common_strip_surface_coordinate_lift BC hBC O hO
  have hEdgeRange (side : Fin 4) (z : Interval × Interval) :
      movie (actualUniformCellGridSide n k side) z ∈ range BC := by
    apply hmovieRange _ _ z
    intro t
    exact hrange k htrue _ (actual_uniform_cell_physical_grid_side_mem n hn cell hcell k side t) 1
  have hex (side : Fin 4) := actual_common_strip_surface_coordinate_lift BC hBC
    (movie (actualUniformCellGridSide n k side)) (hEdgeRange side)
  choose edges hEdges using hex
  have hSide (side : Fin 4) (t : Interval) :
      O (actualLiteralCellSide side t)=R (actualUniformGridEdgeParameter n hn
        (actualUniformCellGridSide n k side) t,1) := by
    change R ((ArcFinitePosition.intervalMeshParameter n hn k.1 (actualLiteralCellSide side t).1,
      ArcFinitePosition.intervalMeshParameter n hn k.2 (actualLiteralCellSide side t).2),1)=_
    rw [actual_literal_cell_side_grid_parameter]
  refine ⟨original,edges,hOriginal,hEdges,?_,?_,?_⟩
  · intro side t
    apply actual_common_strip_decode_injective BC hBC
    change BC (actualStripProductCoordinates.symm (edges side (0,t)))=
      BC (actualStripProductCoordinates.symm (original (actualLiteralCellSide side t)))
    rw [hEdges,hOriginal,hSide,hstart]
  · intro side σ t ht
    apply actual_common_strip_decode_injective BC hBC
    change BC (actualStripProductCoordinates.symm (edges side (σ,t)))=
      BC (actualStripProductCoordinates.symm (original (actualLiteralCellSide side t)))
    rw [hEdges,hOriginal,hSide,hends _ σ t ht]
  · intro side
    have hzero (t : Interval) : (edges side (1,t)).val.2=0 ↔
        movie (actualUniformCellGridSide n k side) (1,t) ∈ old := by
      have hnormal (q : Icc (0:ℝ) 1 ×ˢ Icc (-1:ℝ) 1) :
          ((actualStripProductCoordinates.symm q).2:ℝ)=q.val.2 := rfl
      have hh := (haxis (actualStripProductCoordinates.symm (edges side (1,t)))).symm
      rw [hnormal,hEdges] at hh
      exact hh
    simpa only [hzero] using hfinite (actualUniformCellGridSide n k side)
end CurveComplex.HyperellipticModel
