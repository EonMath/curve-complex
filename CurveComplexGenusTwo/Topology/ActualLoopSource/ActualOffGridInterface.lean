import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualUniformGridInteriorEdgeParameters
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Actual physical interior interfaces incident to an off cell, expressed by
the original produced cell labels and literal grid indices. -/
def actualOffGridInterface (n : ℕ) (label : (Fin n × Fin n) → Bool) :
    ((Fin n × Fin (n+1)) ⊕ (Fin (n+1) × Fin n)) → Prop := fun e =>
  e.elim
    (fun e => ∃ j : Fin n,j.val=e.2.val ∧ 0< j.val ∧
      (label (e.1,j)=false ∨ label (e.1,⟨j.val-1,by omega⟩)=false))
    (fun e => ∃ i : Fin n,i.val=e.1.val ∧ 0< i.val ∧
      (label (i,e.2)=false ∨ label (⟨i.val-1,by omega⟩,e.2)=false))
theorem actual_off_grid_horizontal_interface
    (n : ℕ) (label : (Fin n × Fin n) → Bool)
    (q : {e : Fin n × Fin n // 0< e.2.val}) :
    actualOffGridInterface n label (Sum.inl (q.val.1,q.val.2.castSucc)) ↔
      label q.val=false ∨ label (q.val.1,⟨q.val.2.val-1,by omega⟩)=false := by
  constructor
  · rintro ⟨j,hj,_hpos,hfalse⟩
    have he : j=q.val.2 := Fin.ext hj
    subst j
    exact hfalse
  · intro hfalse
    exact ⟨q.val.2,rfl,q.property,hfalse⟩
theorem actual_off_grid_vertical_interface
    (n : ℕ) (label : (Fin n × Fin n) → Bool)
    (q : {e : Fin n × Fin n // 0< e.1.val}) :
    actualOffGridInterface n label (Sum.inr (q.val.1.castSucc,q.val.2)) ↔
      label q.val=false ∨ label (⟨q.val.1.val-1,by omega⟩,q.val.2)=false := by
  constructor
  · rintro ⟨i,hi,_hpos,hfalse⟩
    have he : i=q.val.1 := Fin.ext hi
    subst i
    exact hfalse
  · intro hfalse
    exact ⟨q.val.1,rfl,q.property,hfalse⟩
end CurveComplex.HyperellipticModel
