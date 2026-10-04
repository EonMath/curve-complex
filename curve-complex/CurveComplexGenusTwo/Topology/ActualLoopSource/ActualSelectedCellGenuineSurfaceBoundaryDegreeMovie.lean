import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSelectedCellGenuineSurfaceMovie
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSelectedCellGenuineContactBoundaryDegreeMovie
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualHomotopyConcatenationAvoidance
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- The actual selected-cell construction lifts its three genuine stages through
the original strip embedding, producing a branch-free surface homotopy and a
complete finite proper contact family, retaining every physical shared edge. -/
theorem actual_selected_cell_genuine_surface_boundary_degree_movie
    {S : Type} [TopologicalSpace S]
    (BC : Interval × Icc (-1:ℝ) 1 → S) (hBC : IsEmbedding BC)
    (forbidden : Set S) (hBCmarks : ∀ z,BC z ∉ forbidden)
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
    ∃ G : C(Interval × Interval,S),
    ∃ H : (actualUniformCellSurfaceMap R n hn k).Homotopy G,
    ∃ middle : C((Interval × Interval) × Interval,S),
    ∃ first : (actualUniformCellSurfaceMap R n hn k).Homotopy
        (⟨fun z => middle (z,0),by fun_prop⟩ : C(Interval × Interval,S)),
    ∃ mid : (⟨fun z => middle (z,0),by fun_prop⟩ : C(Interval × Interval,S)).Homotopy
        (⟨fun z => middle (z,1),by fun_prop⟩ : C(Interval × Interval,S)),
    ∃ last : (⟨fun z => middle (z,1),by fun_prop⟩ : C(Interval × Interval,S)).Homotopy G,
      H=(first.trans mid).trans last ∧
      (∀ σ z,mid (σ,z)=middle (z,σ)) ∧
      (∀ side σ t,middle (actualLiteralCellSide side t,σ)=
        movie (actualUniformCellGridSide n k side) (σ,t)) ∧
      (∀ σ z,z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 →
        first (σ,z)=actualUniformCellSurfaceMap R n hn k z) ∧
      (∀ σ z,z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 → last (σ,z)=G z) ∧
      (∀ σ z,H (σ,z) ∉ forbidden) ∧
    ∃ vertices : Finset (Interval × Interval),
    ∃ A : Type,∃ _hA : Finite A,∃ arc : A → C(Interval,Interval × Interval),
      (∀ e,arc e 0 ∈ vertices ∧ arc e 1 ∈ vertices) ∧
      (∀ e d t u,arc e t=arc d u → (e=d ∧ t=u) ∨ ((t=0 ∨ t=1) ∧ (u=0 ∨ u=1))) ∧
      (∀ e t,t≠0 → t≠1 → arc e t ∉ vertices) ∧
      (∀ e,IsEmbedding (arc e)) ∧
      (∀ e t,0<t.val → t.val<1 →
        0<(arc e t).1.val ∧ (arc e t).1.val<1 ∧ 0<(arc e t).2.val ∧ (arc e t).2.val<1) ∧
      (∀ z,G z ∈ old ↔ z ∈ vertices ∨ ∃ e t,arc e t=z) ∧
      (∀ v : ↑vertices,0<v.val.1.val → v.val.1.val < 1 →
        0<v.val.2.val → v.val.2.val < 1 →
        {r : A × Fin 2 | arc r.1 (if r.2=0 then 0 else 1)=v.val}.ncard=2) ∧
      ∃ coordinate : C(Interval × Interval,Interval × Icc (-1:ℝ) 1),
        (∀ z,BC (coordinate z)=G z) ∧
      (∀ (i : Fin 4) (u : Interval),0<u.val → u.val < 1 →
        (coordinate (actualLiteralCellSide i u)).2.val=0 →
        ∀ δ : ℝ,0<δ →
        (∀ v w : Interval,u.val-δ<v.val → v<u → u<w → w.val<u.val+δ →
          (coordinate (actualLiteralCellSide i v)).2.val/(1/2:ℝ)≠0 ∧
          (coordinate (actualLiteralCellSide i w)).2.val/(1/2:ℝ)≠0 ∧
          ((0<(coordinate (actualLiteralCellSide i v)).2.val/(1/2:ℝ)) ↔
            ¬(0<(coordinate (actualLiteralCellSide i w)).2.val/(1/2:ℝ)))) →
        {r : A × Fin 2 | arc r.1 (if r.2=0 then 0 else 1)=actualLiteralCellSide i u}.ncard=1) := by
  obtain ⟨original,edges,hOriginal,hEdges,hStart,hEnds,hFinite,
    Gc,Hc,Mc,Fc,Mhc,Lc,hH,hmid,hMiddle,hFirst,hLast,
    vertices,A,hA,arc,hArcEnds,hcollision,hclear,hembed,hinterior,hcoverage,hdegree,hboundaryDegree⟩ :=
    actual_selected_cell_genuine_contact_boundary_degree_movie BC hBC old haxis R n hn cell hcell label hrange
      movie hstart hends hfinite hmovieRange k htrue
  let V : Set (ℝ × ℝ) := Icc (0:ℝ) 1 ×ˢ Icc (-1:ℝ) 1
  let decode : C(V,S) := ⟨fun q => BC (actualStripProductCoordinates.symm q),
    hBC.continuous.comp actualStripProductCoordinates.symm.continuous⟩
  let G : C(Interval × Interval,S) := decode.comp Gc
  let middle : C((Interval × Interval) × Interval,S) := decode.comp Mc
  let first : (actualUniformCellSurfaceMap R n hn k).Homotopy
      (⟨fun z => middle (z,0),by fun_prop⟩ : C(Interval × Interval,S)) :=
    { toFun := fun z => decode (Fc z)
      continuous_toFun := decode.continuous.comp Fc.continuous
      map_zero_left := by
        intro z
        exact (congrArg decode (Fc.map_zero_left z)).trans (hOriginal z)
      map_one_left := by
        intro z
        change decode (Fc (1,z))=decode (Mc (z,0))
        exact congrArg decode (Fc.map_one_left z) }
  let mid : (⟨fun z => middle (z,0),by fun_prop⟩ : C(Interval × Interval,S)).Homotopy
      (⟨fun z => middle (z,1),by fun_prop⟩ : C(Interval × Interval,S)) :=
    { toFun := fun z => decode (Mhc z)
      continuous_toFun := decode.continuous.comp Mhc.continuous
      map_zero_left := by
        intro z
        change decode (Mhc (0,z))=decode (Mc (z,0))
        exact congrArg decode (Mhc.map_zero_left z)
      map_one_left := by
        intro z
        change decode (Mhc (1,z))=decode (Mc (z,1))
        exact congrArg decode (Mhc.map_one_left z) }
  let last : (⟨fun z => middle (z,1),by fun_prop⟩ : C(Interval × Interval,S)).Homotopy G :=
    { toFun := fun z => decode (Lc z)
      continuous_toFun := decode.continuous.comp Lc.continuous
      map_zero_left := by
        intro z
        change decode (Lc (0,z))=decode (Mc (z,1))
        exact congrArg decode (Lc.map_zero_left z)
      map_one_left := by
        intro z
        change decode (Lc (1,z))=decode (Gc z)
        exact congrArg decode (Lc.map_one_left z) }
  let H := (first.trans mid).trans last
  refine ⟨G,H,middle,first,mid,last,rfl,?_,?_,?_,?_,?_,vertices,A,hA,arc,
    hArcEnds,hcollision,hclear,hembed,hinterior,?_,hdegree,?_⟩
  · intro σ z
    change decode (Mhc (σ,z))=decode (Mc (z,σ))
    rw [hmid]
  · intro side σ t
    fin_cases side
    · change decode (Mc ((t,0),σ))=movie (actualUniformCellGridSide n k 0) (σ,t)
      rw [(hMiddle σ t).1]
      exact hEdges 0 (σ,t)
    · change decode (Mc ((1,t),σ))=movie (actualUniformCellGridSide n k 1) (σ,t)
      rw [(hMiddle σ t).2.1]
      exact hEdges 1 (σ,t)
    · change decode (Mc ((t,1),σ))=movie (actualUniformCellGridSide n k 2) (σ,t)
      rw [(hMiddle σ t).2.2.1]
      exact hEdges 2 (σ,t)
    · change decode (Mc ((0,t),σ))=movie (actualUniformCellGridSide n k 3) (σ,t)
      rw [(hMiddle σ t).2.2.2]
      exact hEdges 3 (σ,t)
  · intro σ z hz
    change decode (Fc (σ,z))=actualUniformCellSurfaceMap R n hn k z
    rw [hFirst σ z hz]
    exact hOriginal z
  · intro σ z hz
    change decode (Lc (σ,z))=decode (Gc z)
    rw [hLast σ z hz]
  · exact actual_three_stage_concatenation_avoidance first mid last forbidden
      (fun σ z => hBCmarks (actualStripProductCoordinates.symm (Fc (σ,z))))
      (fun σ z => hBCmarks (actualStripProductCoordinates.symm (Mhc (σ,z))))
      (fun σ z => hBCmarks (actualStripProductCoordinates.symm (Lc (σ,z))))
  · intro z
    exact (haxis (actualStripProductCoordinates.symm (Gc z))).trans (hcoverage z)
  · let coordinate : C(Interval × Interval,Interval × Icc (-1:ℝ) 1) :=
      ⟨fun z => actualStripProductCoordinates.symm (Gc z),
        actualStripProductCoordinates.symm.continuous.comp Gc.continuous⟩
    refine ⟨coordinate,fun _ => rfl,?_⟩
    intro i u hu0 hu1 hroot δ hδ hflip
    exact hboundaryDegree i u hu0 hu1 hroot δ hδ hflip
end CurveComplex.HyperellipticModel
