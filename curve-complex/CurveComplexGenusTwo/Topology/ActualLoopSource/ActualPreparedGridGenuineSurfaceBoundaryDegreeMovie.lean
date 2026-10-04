import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSelectedCellGenuineSurfaceBoundaryDegreeMovie
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSelectedCellPhysicalStageBoundary
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualOffCellPhysicalSideLiteral
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualOuterGridCellSides
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualUniformThreeStageSurfaceGluing
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Actual source-selected surface fillings and literal off cells glue jointly,
retaining each constructed finite proper contact family at the final time. -/
theorem actual_prepared_grid_genuine_surface_boundary_degree_movie
    {S : Type} [TopologicalSpace S]
    (BC : Interval × Icc (-1:ℝ) 1 → S) (hBC : IsEmbedding BC)
    (forbidden : Set S) (hBCmarks : ∀ z,BC z ∉ forbidden)
    (old : Set S) (haxis : ∀ z,BC z ∈ old ↔ z.2.val=0)
    (R : C((Interval × Interval) × Interval,S)) (hRmarks : ∀ z,R z ∉ forbidden)
    (n : ℕ) (hn : 0<n)
    (cell : (Fin n × Fin n) → Set (Interval × Interval))
    (hcell : ∀ k,cell k=range (fun z : Interval × Interval =>
      (ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
        ArcFinitePosition.intervalMeshParameter n hn k.2 z.2)))
    (label : (Fin n × Fin n) → Bool)
    (hrange : ∀ k,label k=true → ∀ z ∈ cell k,∀ σ,R (z,σ) ∈ range BC)
    (hoffcell : ∀ k,label k=false → ∀ z : Interval × Interval,
      R ((ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
        ArcFinitePosition.intervalMeshParameter n hn k.2 z.2),1) ∉ old)
    (movie : ((Fin n × Fin (n+1)) ⊕ (Fin (n+1) × Fin n)) → C(Interval × Interval,S))
    (hstart : ∀ e t,movie e (0,t)=R (actualUniformGridEdgeParameter n hn e t,1))
    (hends : ∀ e σ t,t=0 ∨ t=1 → movie e (σ,t)=R (actualUniformGridEdgeParameter n hn e t,1))
    (hfinite : ∀ e,{t : Interval | movie e (1,t) ∈ old}.Finite)
    (hmovieRange : ∀ e,(∀ t,R (actualUniformGridEdgeParameter n hn e t,1) ∈ range BC) →
      ∀ z,movie e z ∈ range BC)
    (hoff : ∀ e,actualOffGridInterface n label e → ∀ σ t,movie e (σ,t)=
      R (actualUniformGridEdgeParameter n hn e t,1))
    (houter : ∀ side i σ t,movie (actualUniformOuterGridEdge n i side) (σ,t)=
      R (actualUniformGridEdgeParameter n hn (actualUniformOuterGridEdge n i side) t,1))
    (B : ((Interval × Interval) × Interval) → S)
    (hB : ∀ e t σ,B (actualUniformGridEdgeParameter n hn e t,σ)=movie e (σ,t)) :
    ∃ final : (Fin n × Fin n) → C(Interval × Interval,S),
    ∃ total : C((Interval × Interval) × Interval,S),
      (∀ z,total (z,0)=R (z,1)) ∧
      (∀ k (z : Interval × Interval),total ((ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
        ArcFinitePosition.intervalMeshParameter n hn k.2 z.2),1)=final k z) ∧
      (∀ z,total z ∉ forbidden) ∧
      (∀ side i σ t,total (actualUniformGridEdgeParameter n hn
        (actualUniformOuterGridEdge n i side) t,σ)=R (actualUniformGridEdgeParameter n hn
          (actualUniformOuterGridEdge n i side) t,1)) ∧
      (∀ k,label k=false → ∀ (z : Interval × Interval) σ,total ((ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
        ArcFinitePosition.intervalMeshParameter n hn k.2 z.2),σ)=R
          ((ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
            ArcFinitePosition.intervalMeshParameter n hn k.2 z.2),1)) ∧
      (∀ k side t,final k (actualLiteralCellSide side t)=
        movie (actualUniformCellGridSide n k side) (1,t)) ∧
      (∀ k,label k=false → ∀ z,final k z ∉ old) ∧
      (∀ k,label k=true → let G := final k; ∃ vertices : Finset (Interval × Interval),
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
        {r : A × Fin 2 | arc r.1 (if r.2=0 then 0 else 1)=actualLiteralCellSide i u}.ncard=1)) := by
  classical
  let f0 := actualUniformCellSurfaceMap R n hn
  let P (k : Fin n × Fin n) (G : C(Interval × Interval,S)) : Prop :=
    (label k=false → ∀ z,G z ∉ old) ∧ (label k=true → ∃ vertices : Finset (Interval × Interval),
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
        {r : A × Fin 2 | arc r.1 (if r.2=0 then 0 else 1)=actualLiteralCellSide i u}.ncard=1))
  have hall (k : Fin n × Fin n) :
      ∃ f1 f2 f3 : C(Interval × Interval,S),
      ∃ first : (f0 k).Homotopy f1,∃ middle : f1.Homotopy f2,∃ last : f2.Homotopy f3,
        (∀ z σ,z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 → first (σ,z)=
          B ((ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
            ArcFinitePosition.intervalMeshParameter n hn k.2 z.2),0)) ∧
        (∀ z σ,z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 → middle (σ,z)=
          B ((ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
            ArcFinitePosition.intervalMeshParameter n hn k.2 z.2),σ)) ∧
        (∀ z σ,z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 → last (σ,z)=
          B ((ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
            ArcFinitePosition.intervalMeshParameter n hn k.2 z.2),1)) ∧
        (∀ σ z,((first.trans middle).trans last) (σ,z) ∉ forbidden) ∧
        (label k=false → ∀ σ z,((first.trans middle).trans last) (σ,z)=f0 k z) ∧
        P k f3 := by
    by_cases hk : label k=true
    · obtain ⟨G,H,Mc,F,Mh,L,hH,hmid,hside,hF,hL,havoid,hprops⟩ :=
        actual_selected_cell_genuine_surface_boundary_degree_movie BC hBC forbidden hBCmarks old haxis
          R n hn cell hcell label hrange movie hstart hends hfinite hmovieRange k hk
      have hside' : ∀ side σ t,Mh (σ,actualLiteralCellSide side t)=
          movie (actualUniformCellGridSide n k side) (σ,t) := by
        intro side σ t
        rw [hmid,hside]
      obtain ⟨hbF,hbM,hbL⟩ := actual_selected_cell_physical_stage_boundary n hn k _ _ _ _
        F Mh L movie B hB hside' hF hL
      refine ⟨_,_,G,F,Mh,L,hbF,hbM,hbL,?_,?_,?_,?_⟩
      · simpa only [←hH] using havoid
      · intro hfalse
        simp [hk] at hfalse
      · intro hfalse
        simp [hk] at hfalse
      · exact fun _ => hprops
    · have hkfalse : label k=false := Bool.eq_false_of_not_eq_true hk
      let H := ContinuousMap.Homotopy.refl (f0 k)
      have hb (z : Interval × Interval) (σ : Interval)
          (hz : z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1) :
          H (σ,z)=B ((ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
            ArcFinitePosition.intervalMeshParameter n hn k.2 z.2),σ) := by
        obtain ⟨side,t,rfl⟩ := actual_literal_cell_boundary_parameter z hz
        change R ((ArcFinitePosition.intervalMeshParameter n hn k.1 (actualLiteralCellSide side t).1,
          ArcFinitePosition.intervalMeshParameter n hn k.2 (actualLiteralCellSide side t).2),1)=_
        rw [actual_literal_cell_side_grid_parameter,hB]
        exact (actual_off_cell_physical_side_literal n hn label
          ⟨fun z => R (z,1),by fun_prop⟩ movie hoff houter k hkfalse side σ t).symm
      have hconst (σ : Interval) (z : Interval × Interval) :
          ((H.trans H).trans H) (σ,z)=f0 k z := by
        rw [ContinuousMap.Homotopy.trans_apply]
        split_ifs
        · rw [ContinuousMap.Homotopy.trans_apply]
          split_ifs <;> rfl
        · rfl
      refine ⟨f0 k,f0 k,f0 k,H,H,H,?_,hb,?_,?_,fun _ => hconst,?_,?_⟩
      · intro z σ hz
        exact hb z 0 hz
      · intro z σ hz
        exact hb z 1 hz
      · intro σ z
        rw [hconst]
        exact hRmarks _
      · exact fun _ => hoffcell k hkfalse
      · intro htrue
        exact False.elim (hk htrue)
  choose f1 f2 f3 first middle last hfirst hmiddle hlast havoid hoffstage hP using hall
  obtain ⟨total,htotal,hzero,hone,hmarks⟩ := actual_uniform_three_stage_surface_gluing
    n hn f0 f1 f2 f3 first middle last B hfirst hmiddle hlast forbidden havoid
  have houterTotal (side : Fin 4) (i : Fin n) (σ t : Interval) :
      total (actualUniformGridEdgeParameter n hn (actualUniformOuterGridEdge n i side) t,σ)=
        R (actualUniformGridEdgeParameter n hn (actualUniformOuterGridEdge n i side) t,1) := by
    obtain ⟨k,hk⟩ := actual_outer_grid_cell_side n hn i side
    let z := actualLiteralCellSide side t
    have hz : z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 := actual_literal_cell_side_boundary side t
    have hp : (ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
        ArcFinitePosition.intervalMeshParameter n hn k.2 z.2)=
          actualUniformGridEdgeParameter n hn (actualUniformOuterGridEdge n i side) t := by
      exact (actual_literal_cell_side_grid_parameter n hn k side t).trans
        (congrArg (fun e => actualUniformGridEdgeParameter n hn e t) hk)
    have hb (τ : Interval) : B ((ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
        ArcFinitePosition.intervalMeshParameter n hn k.2 z.2),τ)=
          R (actualUniformGridEdgeParameter n hn (actualUniformOuterGridEdge n i side) t,1) := by
      rw [hp,hB]
      exact houter side i τ t
    have hF (τ) := (hfirst k z τ hz).trans (hb 0)
    have hM (τ) := (hmiddle k z τ hz).trans (hb τ)
    have hL (τ) := (hlast k z τ hz).trans (hb 1)
    conv_lhs => rw [←hp]
    rw [htotal k z σ,ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · rw [ContinuousMap.Homotopy.trans_apply]
      split_ifs
      · exact hF _
      · exact hM _
    · exact hL _
  have hfinalSide (k : Fin n × Fin n) (side : Fin 4) (t : Interval) :
      f3 k (actualLiteralCellSide side t)=movie (actualUniformCellGridSide n k side) (1,t) := by
    rw [← (last k).map_one_left]
    change last k (1,actualLiteralCellSide side t)=_
    rw [hlast k _ 1 (actual_literal_cell_side_boundary side t)]
    rw [actual_literal_cell_side_grid_parameter,hB]
  refine ⟨f3,total,?_,hone,hmarks,houterTotal,?_,hfinalSide,fun k => (hP k).1,fun k => (hP k).2⟩
  · intro z
    obtain ⟨i,s,hs⟩ := ArcFinitePosition.intervalMeshParameter_cover n hn z.1
    obtain ⟨j,t,ht⟩ := ArcFinitePosition.intervalMeshParameter_cover n hn z.2
    have he : (ArcFinitePosition.intervalMeshParameter n hn i s,
      ArcFinitePosition.intervalMeshParameter n hn j t)=z := Prod.ext hs ht
    rw [←he,hzero (i,j) (s,t)]
    rfl
  · intro k hk z σ
    rw [htotal k z σ,hoffstage k hk σ z]
    rfl
end CurveComplex.HyperellipticModel
