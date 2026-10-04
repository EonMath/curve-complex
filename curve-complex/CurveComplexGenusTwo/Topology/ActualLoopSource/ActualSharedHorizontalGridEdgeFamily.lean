import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSharedHorizontalGridEdgeRedraw
namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- Actual simultaneous horizontal shared-edge family: physical grid edges
between two selected cells index one chosen genuine edge movie, so both incident
cells can consume the same construction. The family is constructed, not given. -/
theorem actual_shared_horizontal_grid_edge_family
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (BC : Interval × Icc (-1:ℝ) 1 → S) (hBC : IsEmbedding BC)
    (hmarks : ∀ z,BC z ∉ (M.cover.branch : Set S))
    (haxis : ∀ z,BC z ∈ a.val.image ↔ z.2.val=0)
    (R : C((Interval × Interval) × Interval,S)) (n : ℕ) (hn : 0<n)
    (cell : (Fin n × Fin n) → Set (Interval × Interval))
    (hcell : ∀ k,cell k=range (fun z : Interval × Interval =>
      (ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
        ArcFinitePosition.intervalMeshParameter n hn k.2 z.2)))
    (label : (Fin n × Fin n) → Bool)
    (hrange : ∀ k,label k=true → ∀ z ∈ cell k,∀ σ,R (z,σ) ∈ range BC)
    (hvertex : ∀ i j : Fin (n+1),(0< i.val ∧ i.val<n) ∨ (0< j.val ∧ j.val<n) →
      R ((actualHalfMeshParameter n hn ⟨2*i.val,by omega⟩,
        actualHalfMeshParameter n hn ⟨2*j.val,by omega⟩),1) ∉ a.val.image)
    : let Index := {e : Fin n × Fin n //
        0< e.2.val ∧ label e=true ∧
          label (e.1,⟨e.2.val-1,by omega⟩)=true}
      ∃ edge : Index → C(Interval,S),∃ H : Index → C(Interval × Interval,S),
        ∀ e,
          (∀ t,H e (0,t)=R ((ArcFinitePosition.intervalMeshParameter n hn e.val.1 t,
            actualHalfMeshParameter n hn ⟨2*e.val.2.val,by omega⟩),1)) ∧
          (∀ t,H e (1,t)=edge e t) ∧
          (∀ σ,H e (σ,0)=R ((ArcFinitePosition.intervalMeshParameter n hn e.val.1 0,
              actualHalfMeshParameter n hn ⟨2*e.val.2.val,by omega⟩),1) ∧
            H e (σ,1)=R ((ArcFinitePosition.intervalMeshParameter n hn e.val.1 1,
              actualHalfMeshParameter n hn ⟨2*e.val.2.val,by omega⟩),1)) ∧
          (∀ z,H e z ∉ (M.cover.branch : Set S)) ∧
          (edge e 0 ∉ a.val.image ∧ edge e 1 ∉ a.val.image) ∧
          {t : Interval | edge e t ∈ a.val.image}.Finite ∧
          (∀ t u,edge e t ∈ a.val.image → edge e u ∈ a.val.image → t=u) ∧
          (∀ t,edge e t ∈ a.val.image → t≠0 ∧ t≠1) := by
  classical
  let Index := {e : Fin n × Fin n //
    0< e.2.val ∧ label e=true ∧ label (e.1,⟨e.2.val-1,by omega⟩)=true}
  have hex (e : Index) := actual_shared_horizontal_grid_edge_redraw M a BC hBC hmarks haxis
    R n hn cell hcell label hrange hvertex e.val.1
    (⟨e.val.2.val,by omega⟩ : Fin (n+1))
    ⟨e.property.1,e.val.2.isLt⟩ e.property.2.1
  choose edge H hH using hex
  exact ⟨edge,H,hH⟩
end CurveComplex.HyperellipticModel
