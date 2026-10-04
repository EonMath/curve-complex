import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualAllInteriorHorizontalGridEdgeAffineMovies
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualAllInteriorVerticalGridEdgeAffineMovies
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualWholeGridEdgeMovieAssemblyWithProperty
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualOffGridInterface
namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- The actual prepared square movie produces one WHOLE physical-grid
edge-movie family and one shared boundary assignment, including literal outer
sides and their original corners. No edge family or assignment is supplied. -/
theorem actual_prepared_loop_whole_grid_affine_edge_movies_in_range
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
    (hRmarks : ∀ z,R z ∉ (M.cover.branch : Set S))
    (hoff : ∀ k,label k=false → ∀ z : Interval × Interval,∀ σ,
      R ((ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
        ArcFinitePosition.intervalMeshParameter n hn k.2 z.2),σ) ∉ a.val.image)
    (hbottom : {t : Interval | R ((t,0),1) ∈ a.val.image}.Finite)
    (hright : {t : Interval | R ((1,t),1) ∈ a.val.image}.Finite)
    (htop : {t : Interval | R ((t,1),1) ∈ a.val.image}.Finite)
    (hleft : {t : Interval | R ((0,t),1) ∈ a.val.image}.Finite) :
    let F : C(Interval × Interval,S) := ⟨fun z => R (z,1),by fun_prop⟩
    let Edge := (Fin n × Fin (n+1)) ⊕ (Fin (n+1) × Fin n)
    ∃ movie : Edge → C(Interval × Interval,S),
      (∀ e t,movie e (0,t)=F (actualUniformGridEdgeParameter n hn e t)) ∧
      (∀ e σ t,t=0 ∨ t=1 → movie e (σ,t)=F (actualUniformGridEdgeParameter n hn e t)) ∧
      (∀ e z,movie e z ∉ (M.cover.branch : Set S)) ∧
      (∀ e,{t : Interval | movie e (1,t) ∈ a.val.image}.Finite) ∧
      (∀ e,(∀ t,F (actualUniformGridEdgeParameter n hn e t) ∈ range BC) →
        ∀ z,movie e z ∈ range BC) ∧
      (∀ e,actualOffGridInterface n label e → ∀ σ t,movie e (σ,t)=
        F (actualUniformGridEdgeParameter n hn e t)) ∧
      (∀ side i σ t,movie (actualUniformOuterGridEdge n i side) (σ,t)=
        F (actualUniformGridEdgeParameter n hn (actualUniformOuterGridEdge n i side) t)) ∧
    (∀ e,(e.elim (fun q => 0<q.2.val ∧ q.2.val<n) (fun q => 0<q.1.val ∧ q.1.val<n) → ∀ u,movie e (1,u)∈a.val.image →
        ∃ finalQ : C(Interval,range BC),(∀ t,(finalQ t).val=movie e (1,t)) ∧
        (∀ v w,v<u → u<w →
          (hBC.toHomeomorph.symm (finalQ v)).2.val≠0 ∧
          (hBC.toHomeomorph.symm (finalQ w)).2.val≠0 ∧
          ((0<(hBC.toHomeomorph.symm (finalQ v)).2.val) ↔
            ¬(0<(hBC.toHomeomorph.symm (finalQ w)).2.val))))) ∧
    ∃ B : ((Interval × Interval) × Interval) → S,
      ∀ e t σ,B (actualUniformGridEdgeParameter n hn e t,σ)=movie e (σ,t) := by
  let F : C(Interval × Interval,S) := ⟨fun z => R (z,1),by fun_prop⟩
  obtain ⟨Eh,Hh,hHh⟩ := actual_all_interior_horizontal_grid_edge_affine_movies
    M a BC hBC hmarks haxis R n hn cell hcell label hrange hvertex hRmarks hoff
  obtain ⟨Ev,Hv,hHv⟩ := actual_all_interior_vertical_grid_edge_affine_movies
    M a BC hBC hmarks haxis R n hn cell hcell label hrange hvertex hRmarks hoff
  have hHs := fun e => (hHh e).1
  have hVs := fun e => (hHv e).1
  have hHe (e) (σ t : Interval) (ht : t=0 ∨ t=1) : Hh e (σ,t)=
      F (ArcFinitePosition.intervalMeshParameter n hn e.val.1 t,
        ArcFinitePosition.intervalMeshParameter n hn e.val.2 0) := by
    rcases ht with rfl | rfl
    · exact ((hHh e).2.2.1 σ).1
    · exact ((hHh e).2.2.1 σ).2
  have hVe (e) (σ t : Interval) (ht : t=0 ∨ t=1) : Hv e (σ,t)=
      F (ArcFinitePosition.intervalMeshParameter n hn e.val.1 0,
        ArcFinitePosition.intervalMeshParameter n hn e.val.2 t) := by
    rcases ht with rfl | rfl
    · exact ((hHv e).2.2.1 σ).1
    · exact ((hHv e).2.2.1 σ).2
  have hHf (e) : {t : Interval | Hh e (1,t) ∈ a.val.image}.Finite := by
    simpa only [(hHh e).2.1] using (hHh e).2.2.2.2.2.1
  have hVf (e) : {t : Interval | Hv e (1,t) ∈ a.val.image}.Finite := by
    simpa only [(hHv e).2.1] using (hHv e).2.2.2.2.2.1
  let P : ((Fin n × Fin (n+1)) ⊕ (Fin (n+1) × Fin n)) →
      C(Interval × Interval,S) → Prop := fun e H =>
    ((∀ t,F (actualUniformGridEdgeParameter n hn e t) ∈ range BC) → ∀ z,H z ∈ range BC) ∧
    (actualOffGridInterface n label e → ∀ σ t,H (σ,t)=F (actualUniformGridEdgeParameter n hn e t)) ∧
    (e.elim (fun q => 0<q.2.val ∧ q.2.val<n) (fun q => 0<q.1.val ∧ q.1.val<n) → ∀ u,H (1,u)∈a.val.image →
        ∃ finalQ : C(Interval,range BC),(∀ t,(finalQ t).val=H (1,t)) ∧
        (∀ v w,v<u → u<w →
          (hBC.toHomeomorph.symm (finalQ v)).2.val≠0 ∧
          (hBC.toHomeomorph.symm (finalQ w)).2.val≠0 ∧
          ((0<(hBC.toHomeomorph.symm (finalQ v)).2.val) ↔
            ¬(0<(hBC.toHomeomorph.symm (finalQ w)).2.val))))
  have hPH (q : {e : Fin n × Fin n // 0< e.2.val}) :
      P (Sum.inl (q.val.1,q.val.2.castSucc)) (Hh q) := by
    refine ⟨?_,?_,?_⟩
    · intro hOldRange z
      by_cases hu : label q.val=true
      · exact (hHh q).2.2.2.2.1 hu z
      · have hf : label q.val=false := Bool.eq_false_of_not_eq_true hu
        have hstay := (hHh q).2.2.2.2.2.2.2.2.1 (Or.inl hf) z.1 z.2
        change Hh q (z.1,z.2) ∈ range BC
        rw [hstay]
        simpa [F,actual_uniform_grid_horizontal_interior_parameter] using hOldRange z.2
    · intro hf σ t
      have hstay := (hHh q).2.2.2.2.2.2.2.2.1
        ((actual_off_grid_horizontal_interface n label q).mp hf) σ t
      simpa [F,actual_uniform_grid_horizontal_interior_parameter] using hstay
    · intro hi u hu
      obtain ⟨Q,hQ,hflip⟩ := (hHh q).2.2.2.2.2.2.2.2.2 u (by simpa only [(hHh q).2.1] using hu)
      exact ⟨Q,fun t => (hQ t).trans ((hHh q).2.1 t).symm,hflip⟩
  have hPV (q : {e : Fin n × Fin n // 0< e.1.val}) :
      P (Sum.inr (q.val.1.castSucc,q.val.2)) (Hv q) := by
    refine ⟨?_,?_,?_⟩
    · intro hOldRange z
      by_cases hu : label q.val=true
      · exact (hHv q).2.2.2.2.1 hu z
      · have hf : label q.val=false := Bool.eq_false_of_not_eq_true hu
        have hstay := (hHv q).2.2.2.2.2.2.2.2.1 (Or.inl hf) z.1 z.2
        change Hv q (z.1,z.2) ∈ range BC
        rw [hstay]
        simpa [F,actual_uniform_grid_vertical_interior_parameter] using hOldRange z.2
    · intro hf σ t
      have hstay := (hHv q).2.2.2.2.2.2.2.2.1
        ((actual_off_grid_vertical_interface n label q).mp hf) σ t
      simpa [F,actual_uniform_grid_vertical_interior_parameter] using hstay
    · intro hi u hu
      obtain ⟨Q,hQ,hflip⟩ := (hHv q).2.2.2.2.2.2.2.2.2 u (by simpa only [(hHv q).2.1] using hu)
      exact ⟨Q,fun t => (hQ t).trans ((hHv q).2.1 t).symm,hflip⟩
  have hPO (side : Fin 4) (i : Fin n) :
      P (actualUniformOuterGridEdge n i side)
        ((F.comp (actualUniformGridEdgeParameter n hn (actualUniformOuterGridEdge n i side))).comp
          (ContinuousMap.snd : C(Interval × Interval,Interval))) := by
    refine ⟨fun hOldRange z => hOldRange z.2,fun _ _ _ => rfl,?_⟩
    intro hi
    fin_cases side <;> simp [actualUniformOuterGridEdge] at hi
  obtain ⟨movie,hstart,hends,havoid,hfinite,hP,houter,B,hB⟩ :=
    actual_whole_grid_edge_movie_assembly_with_property a.val.image (M.cover.branch : Set S)
      F (fun z => hRmarks (z,1)) hbottom hright htop hleft n hn P Hh Hv hHs hVs hHe hVe
      (fun e => (hHh e).2.2.2.1) (fun e => (hHv e).2.2.2.1) hHf hVf hPH hPV hPO
  exact ⟨movie,hstart,hends,havoid,hfinite,(fun e => (hP e).1),
    (fun e => (hP e).2.1),houter,(fun e => (hP e).2.2),B,hB⟩
end CurveComplex.HyperellipticModel
