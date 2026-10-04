import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSelectedCellFourEdgeCoordinates
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualFourEdgeFiniteContactBoundaryDegreeCellMovie
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Actual prepared selected cell: construct its four shared-edge coordinates,
choose a genuine nonzero strip pole, fill with a finite proper contact family,
and construct three matching stages from the actual original coordinate cell.
No coordinate map, contact family, filling, or cell homotopy is assumed. -/
theorem actual_selected_cell_genuine_contact_boundary_degree_movie
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
      (∀ side,{t : Interval | (edges side (1,t)).val.2=0}.Finite) ∧
    ∃ G : C(Interval × Interval,Icc (0:ℝ) 1 ×ˢ Icc (-1:ℝ) 1),∃ H : original.Homotopy G,
    ∃ middle : C((Interval × Interval) × Interval,Icc (0:ℝ) 1 ×ˢ Icc (-1:ℝ) 1),
    ∃ first : original.Homotopy
        (⟨fun z => middle (z,0),by fun_prop⟩ : C(Interval × Interval,Icc (0:ℝ) 1 ×ˢ Icc (-1:ℝ) 1)),
    ∃ mid : (⟨fun z => middle (z,0),by fun_prop⟩ : C(Interval × Interval,Icc (0:ℝ) 1 ×ˢ Icc (-1:ℝ) 1)).Homotopy
        (⟨fun z => middle (z,1),by fun_prop⟩ : C(Interval × Interval,Icc (0:ℝ) 1 ×ˢ Icc (-1:ℝ) 1)),
    ∃ last : (⟨fun z => middle (z,1),by fun_prop⟩ : C(Interval × Interval,Icc (0:ℝ) 1 ×ˢ Icc (-1:ℝ) 1)).Homotopy G,
      H=(first.trans mid).trans last ∧
      (∀ σ z,mid (σ,z)=middle (z,σ)) ∧
      (∀ σ t,middle ((t,0),σ)=edges 0 (σ,t) ∧
        middle ((1,t),σ)=edges 1 (σ,t) ∧ middle ((t,1),σ)=edges 2 (σ,t) ∧
        middle ((0,t),σ)=edges 3 (σ,t)) ∧
      (∀ σ z,z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 → first (σ,z)=original z) ∧
      (∀ σ z,z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 → last (σ,z)=G z) ∧
    ∃ vertices : Finset (Interval × Interval),
    ∃ A : Type,∃ _hA : Finite A,∃ arc : A → C(Interval,Interval × Interval),
      (∀ e,arc e 0 ∈ vertices ∧ arc e 1 ∈ vertices) ∧
      (∀ e d t u,arc e t=arc d u → (e=d ∧ t=u) ∨ ((t=0 ∨ t=1) ∧ (u=0 ∨ u=1))) ∧
      (∀ e t,t≠0 → t≠1 → arc e t ∉ vertices) ∧
      (∀ e,IsEmbedding (arc e)) ∧
      (∀ e t,0<t.val → t.val<1 →
        0<(arc e t).1.val ∧ (arc e t).1.val<1 ∧ 0<(arc e t).2.val ∧ (arc e t).2.val<1) ∧
      (∀ z,(G z).val.2=0 ↔ z ∈ vertices ∨ ∃ e t,arc e t=z) ∧
      (∀ v : ↑vertices,0<v.val.1.val → v.val.1.val < 1 →
        0<v.val.2.val → v.val.2.val < 1 →
        {r : A × Fin 2 | arc r.1 (if r.2=0 then 0 else 1)=v.val}.ncard=2) ∧
      (∀ (i : Fin 4) (u : Interval),0<u.val → u.val < 1 →
        (G (actualLiteralCellSide i u)).val.2=0 →
        ∀ δ : ℝ,0<δ →
        (∀ v w : Interval,u.val-δ<v.val → v<u → u<w → w.val<u.val+δ →
          (G (actualLiteralCellSide i v)).val.2/(1/2:ℝ)≠0 ∧
          (G (actualLiteralCellSide i w)).val.2/(1/2:ℝ)≠0 ∧
          ((0<(G (actualLiteralCellSide i v)).val.2/(1/2:ℝ)) ↔
            ¬(0<(G (actualLiteralCellSide i w)).val.2/(1/2:ℝ)))) →
        {r : A × Fin 2 | arc r.1 (if r.2=0 then 0 else 1)=actualLiteralCellSide i u}.ncard=1) := by
  obtain ⟨original,edges,hOriginal,hEdges,hStart,hEnds,hFinite⟩ :=
    actual_selected_cell_four_edge_coordinates BC hBC old haxis R n hn cell hcell label hrange
      movie hstart hends hfinite hmovieRange k htrue
  let V : Set (ℝ × ℝ) := Icc (0:ℝ) 1 ×ˢ Icc (-1:ℝ) 1
  have hV : Convex ℝ V := (convex_Icc (0:ℝ) 1).prod (convex_Icc (-1:ℝ) 1)
  let center : V := ⟨(1/2,1/2),by constructor <;> constructor <;> norm_num⟩
  have hc : center.val.2≠0 := by norm_num [center]
  have hb (σ) : edges 0 (σ,0)=original (0,0) ∧ edges 0 (σ,1)=original (1,0) := by
    constructor
    · simpa [actualLiteralCellSide] using hEnds 0 σ 0 (Or.inl rfl)
    · simpa [actualLiteralCellSide] using hEnds 0 σ 1 (Or.inr rfl)
  have hr (σ) : edges 1 (σ,0)=original (1,0) ∧ edges 1 (σ,1)=original (1,1) := by
    constructor
    · simpa [actualLiteralCellSide] using hEnds 1 σ 0 (Or.inl rfl)
    · simpa [actualLiteralCellSide] using hEnds 1 σ 1 (Or.inr rfl)
  have ht (σ) : edges 2 (σ,0)=original (0,1) ∧ edges 2 (σ,1)=original (1,1) := by
    constructor
    · simpa [actualLiteralCellSide] using hEnds 2 σ 0 (Or.inl rfl)
    · simpa [actualLiteralCellSide] using hEnds 2 σ 1 (Or.inr rfl)
  have hl (σ) : edges 3 (σ,0)=original (0,0) ∧ edges 3 (σ,1)=original (0,1) := by
    constructor
    · simpa [actualLiteralCellSide] using hEnds 3 σ 0 (Or.inl rfl)
    · simpa [actualLiteralCellSide] using hEnds 3 σ 1 (Or.inr rfl)
  have hs (t) : edges 0 (0,t)=original (t,0) ∧ edges 1 (0,t)=original (1,t) ∧
      edges 2 (0,t)=original (t,1) ∧ edges 3 (0,t)=original (0,t) := by
    exact ⟨by simpa [actualLiteralCellSide] using hStart 0 t,
      by simpa [actualLiteralCellSide] using hStart 1 t,
      by simpa [actualLiteralCellSide] using hStart 2 t,
      by simpa [actualLiteralCellSide] using hStart 3 t⟩
  obtain ⟨G,H,middle,first,mid,last,hH,hmid,hMiddle,hFirst,hLast,
    vertices,A,hA,arc,hArcEnds,hcollision,hclear,hembed,hinterior,hcoverage,hdegree,hboundaryDegree⟩ :=
    actual_four_edge_finite_contact_boundary_degree_cell_movie V hV original (edges 0) (edges 1) (edges 2) (edges 3)
      hb hr ht hl hs (hFinite 0) (hFinite 1) (hFinite 2) (hFinite 3) center hc
  exact ⟨original,edges,hOriginal,hEdges,hStart,hEnds,hFinite,G,H,middle,first,mid,last,
    hH,hmid,hMiddle,hFirst,hLast,vertices,A,hA,arc,hArcEnds,hcollision,hclear,hembed,hinterior,hcoverage,hdegree,hboundaryDegree⟩
end CurveComplex.HyperellipticModel
