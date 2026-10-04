import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualUniformCellPhysicalGridSides
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Every physical side of an actual off cell is literal for the whole movie:
interior sides use the produced off-interface clause and outer sides use the
produced outer-edge clause. The four original corners are included. -/
theorem actual_off_cell_physical_side_literal
    {S : Type} [TopologicalSpace S]
    (n : ℕ) (hn : 0<n) (label : (Fin n × Fin n) → Bool)
    (F : C(Interval × Interval,S))
    (movie : ((Fin n × Fin (n+1)) ⊕ (Fin (n+1) × Fin n)) → C(Interval × Interval,S))
    (hoff : ∀ e,actualOffGridInterface n label e → ∀ σ t,movie e (σ,t)=
      F (actualUniformGridEdgeParameter n hn e t))
    (houter : ∀ side i σ t,movie (actualUniformOuterGridEdge n i side) (σ,t)=
      F (actualUniformGridEdgeParameter n hn (actualUniformOuterGridEdge n i side) t))
    (k : Fin n × Fin n) (hk : label k=false) (side : Fin 4) (σ t : Interval) :
    movie (actualUniformCellGridSide n k side) (σ,t)=
      F (actualUniformGridEdgeParameter n hn (actualUniformCellGridSide n k side) t) := by
  fin_cases side <;> dsimp only
  · by_cases h : k.2.val=0
    · have he : actualUniformCellGridSide n k 0=actualUniformOuterGridEdge n k.1 0 := by
        simp [actualUniformCellGridSide,actualUniformOuterGridEdge,Fin.ext_iff,h]
      exact (congrArg (fun e => movie e (σ,t)) he).trans
        ((houter 0 k.1 σ t).trans
          (congrArg (fun e => F (actualUniformGridEdgeParameter n hn e t)) he).symm)
    · apply hoff _ ?_ σ t
      change ∃ j : Fin n,j.val = k.2.val ∧ 0 < j.val ∧
        (label (k.1,j)=false ∨ label (k.1,⟨j.val-1,by omega⟩)=false)
      exact ⟨k.2,rfl,by omega,Or.inl hk⟩
  · by_cases h : k.1.val+1=n
    · have he : actualUniformCellGridSide n k 1=actualUniformOuterGridEdge n k.2 1 := by
        simp [actualUniformCellGridSide,actualUniformOuterGridEdge,Fin.ext_iff,h]
      exact (congrArg (fun e => movie e (σ,t)) he).trans
        ((houter 1 k.2 σ t).trans
          (congrArg (fun e => F (actualUniformGridEdgeParameter n hn e t)) he).symm)
    · apply hoff _ ?_ σ t
      change ∃ i : Fin n,i.val = (k.1.val+1) ∧ 0 < i.val ∧
        (label (i,k.2)=false ∨ label (⟨i.val-1,by omega⟩,k.2)=false)
      let i : Fin n := ⟨k.1.val+1,by omega⟩
      refine ⟨i,rfl,by change 0 < k.1.val+1; omega,Or.inr ?_⟩
      have he : (⟨i.val-1,by omega⟩ : Fin n)=k.1 := Fin.ext (by dsimp [i])
      rw [he]
      exact hk
  · by_cases h : k.2.val+1=n
    · have he : actualUniformCellGridSide n k 2=actualUniformOuterGridEdge n k.1 2 := by
        simp [actualUniformCellGridSide,actualUniformOuterGridEdge,Fin.ext_iff,h]
      exact (congrArg (fun e => movie e (σ,t)) he).trans
        ((houter 2 k.1 σ t).trans
          (congrArg (fun e => F (actualUniformGridEdgeParameter n hn e t)) he).symm)
    · apply hoff _ ?_ σ t
      change ∃ j : Fin n,j.val = (k.2.val+1) ∧ 0 < j.val ∧
        (label (k.1,j)=false ∨ label (k.1,⟨j.val-1,by omega⟩)=false)
      let j : Fin n := ⟨k.2.val+1,by omega⟩
      refine ⟨j,rfl,by change 0 < k.2.val+1; omega,Or.inr ?_⟩
      have he : (⟨j.val-1,by omega⟩ : Fin n)=k.2 := Fin.ext (by dsimp [j])
      rw [he]
      exact hk
  · by_cases h : k.1.val=0
    · have he : actualUniformCellGridSide n k 3=actualUniformOuterGridEdge n k.2 3 := by
        simp [actualUniformCellGridSide,actualUniformOuterGridEdge,Fin.ext_iff,h]
      exact (congrArg (fun e => movie e (σ,t)) he).trans
        ((houter 3 k.2 σ t).trans
          (congrArg (fun e => F (actualUniformGridEdgeParameter n hn e t)) he).symm)
    · apply hoff _ ?_ σ t
      change ∃ i : Fin n,i.val = k.1.val ∧ 0 < i.val ∧
        (label (i,k.2)=false ∨ label (⟨i.val-1,by omega⟩,k.2)=false)
      exact ⟨k.1,rfl,by omega,Or.inl hk⟩
end CurveComplex.HyperellipticModel
