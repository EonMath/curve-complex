import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualUniformGridInteriorEdgeParameters
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Assemble actual interior seam movies and the constructed literal outer
movies into one whole physical-grid family, and construct its shared assignment.
The actual affine grid geometry derives all overlap compatibility. Additional
local properties of the constructed component movies are retained. -/
theorem actual_whole_grid_edge_movie_assembly_with_property
    {Y : Type} [TopologicalSpace Y] (old forbidden : Set Y)
    (F : C(Interval × Interval,Y)) (hmarks : ∀ z,F z ∉ forbidden)
    (hbottom : {t : Interval | F (t,0) ∈ old}.Finite)
    (hright : {t : Interval | F (1,t) ∈ old}.Finite)
    (htop : {t : Interval | F (t,1) ∈ old}.Finite)
    (hleft : {t : Interval | F (0,t) ∈ old}.Finite)
    (n : ℕ) (hn : 0<n)
    (P : ((Fin n × Fin (n+1)) ⊕ (Fin (n+1) × Fin n)) → C(Interval × Interval,Y) → Prop)
    (Hh : {e : Fin n × Fin n // 0< e.2.val} → C(Interval × Interval,Y))
    (Hv : {e : Fin n × Fin n // 0< e.1.val} → C(Interval × Interval,Y))
    (hHs : ∀ e t,Hh e (0,t)=F (ArcFinitePosition.intervalMeshParameter n hn e.val.1 t,
      ArcFinitePosition.intervalMeshParameter n hn e.val.2 0))
    (hVs : ∀ e t,Hv e (0,t)=F (ArcFinitePosition.intervalMeshParameter n hn e.val.1 0,
      ArcFinitePosition.intervalMeshParameter n hn e.val.2 t))
    (hHe : ∀ e σ t,t=0 ∨ t=1 → Hh e (σ,t)=
      F (ArcFinitePosition.intervalMeshParameter n hn e.val.1 t,
        ArcFinitePosition.intervalMeshParameter n hn e.val.2 0))
    (hVe : ∀ e σ t,t=0 ∨ t=1 → Hv e (σ,t)=
      F (ArcFinitePosition.intervalMeshParameter n hn e.val.1 0,
        ArcFinitePosition.intervalMeshParameter n hn e.val.2 t))
    (hHm : ∀ e z,Hh e z ∉ forbidden) (hVm : ∀ e z,Hv e z ∉ forbidden)
    (hHf : ∀ e,{t : Interval | Hh e (1,t) ∈ old}.Finite)
    (hVf : ∀ e,{t : Interval | Hv e (1,t) ∈ old}.Finite)
    (hPH : ∀ e,P (Sum.inl (e.val.1,e.val.2.castSucc)) (Hh e))
    (hPV : ∀ e,P (Sum.inr (e.val.1.castSucc,e.val.2)) (Hv e))
    (hPO : ∀ side i,P (actualUniformOuterGridEdge n i side)
      ((F.comp (actualUniformGridEdgeParameter n hn (actualUniformOuterGridEdge n i side))).comp
        (ContinuousMap.snd : C(Interval × Interval,Interval)))) :
    let Edge := (Fin n × Fin (n+1)) ⊕ (Fin (n+1) × Fin n)
    ∃ movie : Edge → C(Interval × Interval,Y),
      (∀ e t,movie e (0,t)=F (actualUniformGridEdgeParameter n hn e t)) ∧
      (∀ e σ t,t=0 ∨ t=1 → movie e (σ,t)=F (actualUniformGridEdgeParameter n hn e t)) ∧
      (∀ e z,movie e z ∉ forbidden) ∧
      (∀ e,{t : Interval | movie e (1,t) ∈ old}.Finite) ∧
      (∀ e,P e (movie e)) ∧
      (∀ side i σ t,movie (actualUniformOuterGridEdge n i side) (σ,t)=
        F (actualUniformGridEdgeParameter n hn (actualUniformOuterGridEdge n i side) t)) ∧
    ∃ B : ((Interval × Interval) × Interval) → Y,
      ∀ e t σ,B (actualUniformGridEdgeParameter n hn e t,σ)=movie e (σ,t) := by
  classical
  let Edge := (Fin n × Fin (n+1)) ⊕ (Fin (n+1) × Fin n)
  let outer : Edge → Prop := fun e =>
    e.elim (fun e => e.2.val=0 ∨ e.2.val=n) (fun e => e.1.val=0 ∨ e.1.val=n)
  obtain ⟨O,hO,hOm,hOf⟩ := actual_outer_grid_edge_literal_movies
    old forbidden F hmarks hbottom hright htop hleft n hn
  have hex (e : Edge) : ∃ H : C(Interval × Interval,Y),
      (∀ t,H (0,t)=F (actualUniformGridEdgeParameter n hn e t)) ∧
      (∀ σ t,t=0 ∨ t=1 → H (σ,t)=F (actualUniformGridEdgeParameter n hn e t)) ∧
      (∀ z,H z ∉ forbidden) ∧ {t : Interval | H (1,t) ∈ old}.Finite ∧ P e H ∧
      (outer e → ∀ σ t,H (σ,t)=F (actualUniformGridEdgeParameter n hn e t)) := by
    have hout (side : Fin 4) (i : Fin n) (he : e=actualUniformOuterGridEdge n i side) :
        ∃ H : C(Interval × Interval,Y),
        (∀ t,H (0,t)=F (actualUniformGridEdgeParameter n hn e t)) ∧
        (∀ σ t,t=0 ∨ t=1 → H (σ,t)=F (actualUniformGridEdgeParameter n hn e t)) ∧
        (∀ z,H z ∉ forbidden) ∧ {t : Interval | H (1,t) ∈ old}.Finite ∧ P e H ∧
        (outer e → ∀ σ t,H (σ,t)=F (actualUniformGridEdgeParameter n hn e t)) := by
      subst e
      have heq : O side i=
          ((F.comp (actualUniformGridEdgeParameter n hn (actualUniformOuterGridEdge n i side))).comp
            (ContinuousMap.snd : C(Interval × Interval,Interval))) := by
        ext z
        exact hO side i z.1 z.2
      exact ⟨O side i,hO side i 0,(fun σ t _ => hO side i σ t),hOm side i,
        hOf side i,(heq.symm ▸ hPO side i),(fun _ => hO side i)⟩
    cases e with
    | inl e =>
      by_cases hz : e.2.val=0
      · apply hout 0 e.1
        apply congrArg Sum.inl
        exact Prod.ext rfl (Fin.ext hz)
      · by_cases hj : e.2.val<n
        · let q : {e : Fin n × Fin n // 0< e.2.val} :=
            ⟨(e.1,⟨e.2.val,hj⟩),by change 0< e.2.val; omega⟩
          have hp (t) : actualUniformGridEdgeParameter n hn (Sum.inl e) t=
              (ArcFinitePosition.intervalMeshParameter n hn q.val.1 t,
                ArcFinitePosition.intervalMeshParameter n hn q.val.2 0) := by
            have he : e=(q.val.1,q.val.2.castSucc) := Prod.ext rfl (Fin.ext rfl)
            rw [he]
            exact actual_uniform_grid_horizontal_interior_parameter n hn q.val t
          refine ⟨Hh q,?_,?_,hHm q,hHf q,?_,?_⟩
          · intro t; rw [hp]; exact hHs q t
          · intro σ t ht; rw [hp]; exact hHe q σ t ht
          · have he : e=(q.val.1,q.val.2.castSucc) := Prod.ext rfl (Fin.ext rfl)
            rw [he]
            exact hPH q
          · intro ho
            change e.2.val=0 ∨ e.2.val=n at ho
            omega
        · apply hout 2 e.1
          apply congrArg Sum.inl
          refine Prod.ext rfl (Fin.ext ?_)
          change e.2.val=n
          have hb := e.2.isLt
          omega
    | inr e =>
      by_cases hz : e.1.val=0
      · apply hout 3 e.2
        apply congrArg Sum.inr
        exact Prod.ext (Fin.ext hz) rfl
      · by_cases hj : e.1.val<n
        · let q : {e : Fin n × Fin n // 0< e.1.val} :=
            ⟨(⟨e.1.val,hj⟩,e.2),by change 0< e.1.val; omega⟩
          have hp (t) : actualUniformGridEdgeParameter n hn (Sum.inr e) t=
              (ArcFinitePosition.intervalMeshParameter n hn q.val.1 0,
                ArcFinitePosition.intervalMeshParameter n hn q.val.2 t) := by
            have he : e=(q.val.1.castSucc,q.val.2) := Prod.ext (Fin.ext rfl) rfl
            rw [he]
            exact actual_uniform_grid_vertical_interior_parameter n hn q.val t
          refine ⟨Hv q,?_,?_,hVm q,hVf q,?_,?_⟩
          · intro t; rw [hp]; exact hVs q t
          · intro σ t ht; rw [hp]; exact hVe q σ t ht
          · have he : e=(q.val.1.castSucc,q.val.2) := Prod.ext (Fin.ext rfl) rfl
            rw [he]
            exact hPV q
          · intro ho
            change e.1.val=0 ∨ e.1.val=n at ho
            omega
        · apply hout 1 e.2
          apply congrArg Sum.inr
          refine Prod.ext (Fin.ext ?_) rfl
          change e.1.val=n
          have hb := e.1.isLt
          omega
  choose movie hstart hends havoid hfinite hP houter using hex
  obtain ⟨B,hB,hBoff⟩ := actual_uniform_grid_shared_boundary_assignment F n hn movie hends
  refine ⟨movie,hstart,hends,havoid,hfinite,hP,?_,B,hB⟩
  intro side i σ t
  apply houter _ _ σ t
  fin_cases side <;> simp [outer,actualUniformOuterGridEdge]
end CurveComplex.HyperellipticModel
