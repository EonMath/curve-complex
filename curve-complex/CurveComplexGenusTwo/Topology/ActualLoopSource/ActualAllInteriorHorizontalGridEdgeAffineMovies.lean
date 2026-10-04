import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualUniformMeshAdjacentSeam
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSharedHorizontalGridEdgeAffineRedrawInRange
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualCommonStripFiniteEdgeRedrawInRange
namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- Every interior horizontal seam is assigned one actual movie. Selected/
selected seams are genuinely redrawn; seams incident to an off cell stay literal
and are proved old-free. Thus all final seam contacts are finite. -/
theorem actual_all_interior_horizontal_grid_edge_affine_movies
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
        ArcFinitePosition.intervalMeshParameter n hn k.2 z.2),σ) ∉ a.val.image) :
    let Index := {e : Fin n × Fin n // 0< e.2.val}
    ∃ edge : Index → C(Interval,S),∃ H : Index → C(Interval × Interval,S),
      ∀ e,
        (∀ t,H e (0,t)=R ((ArcFinitePosition.intervalMeshParameter n hn e.val.1 t,
          ArcFinitePosition.intervalMeshParameter n hn e.val.2 0),1)) ∧
        (∀ t,H e (1,t)=edge e t) ∧
        (∀ σ,H e (σ,0)=R ((ArcFinitePosition.intervalMeshParameter n hn e.val.1 0,
            ArcFinitePosition.intervalMeshParameter n hn e.val.2 0),1) ∧
          H e (σ,1)=R ((ArcFinitePosition.intervalMeshParameter n hn e.val.1 1,
            ArcFinitePosition.intervalMeshParameter n hn e.val.2 0),1)) ∧
        (∀ z,H e z ∉ (M.cover.branch : Set S)) ∧
        (label e.val=true → ∀ z,H e z ∈ range BC) ∧
        {t : Interval | edge e t ∈ a.val.image}.Finite ∧
        (∀ t u,edge e t ∈ a.val.image → edge e u ∈ a.val.image → t=u) ∧
        (∀ t,edge e t ∈ a.val.image → t≠0 ∧ t≠1) ∧
        ((label e.val=false ∨ label (e.val.1,⟨e.val.2.val-1,by omega⟩)=false) →
          ∀ σ t,H e (σ,t)=R ((ArcFinitePosition.intervalMeshParameter n hn e.val.1 t,
            ArcFinitePosition.intervalMeshParameter n hn e.val.2 0),1)) ∧
        (∀ u,edge e u∈a.val.image →
          ∃ finalQ : C(Interval,range BC),(∀ t,(finalQ t).val=edge e t) ∧
          (∀ v w,v<u → u<w →
            (hBC.toHomeomorph.symm (finalQ v)).2.val≠0 ∧
            (hBC.toHomeomorph.symm (finalQ w)).2.val≠0 ∧
            ((0<(hBC.toHomeomorph.symm (finalQ v)).2.val) ↔
              ¬(0<(hBC.toHomeomorph.symm (finalQ w)).2.val)))) := by
  classical
  let Index := {e : Fin n × Fin n // 0< e.2.val}
  have hex (e : Index) : ∃ edge : C(Interval,S),∃ H : C(Interval × Interval,S),
      (∀ t,H (0,t)=R ((ArcFinitePosition.intervalMeshParameter n hn e.val.1 t,
        ArcFinitePosition.intervalMeshParameter n hn e.val.2 0),1)) ∧
      (∀ t,H (1,t)=edge t) ∧
      (∀ σ,H (σ,0)=R ((ArcFinitePosition.intervalMeshParameter n hn e.val.1 0,
          ArcFinitePosition.intervalMeshParameter n hn e.val.2 0),1) ∧
        H (σ,1)=R ((ArcFinitePosition.intervalMeshParameter n hn e.val.1 1,
          ArcFinitePosition.intervalMeshParameter n hn e.val.2 0),1)) ∧
      (∀ z,H z ∉ (M.cover.branch : Set S)) ∧
      (label e.val=true → ∀ z,H z ∈ range BC) ∧
      {t : Interval | edge t ∈ a.val.image}.Finite ∧
      (∀ t u,edge t ∈ a.val.image → edge u ∈ a.val.image → t=u) ∧
      (∀ t,edge t ∈ a.val.image → t≠0 ∧ t≠1) ∧
      ((label e.val=false ∨ label (e.val.1,⟨e.val.2.val-1,by omega⟩)=false) →
        ∀ σ t,H (σ,t)=R ((ArcFinitePosition.intervalMeshParameter n hn e.val.1 t,
          ArcFinitePosition.intervalMeshParameter n hn e.val.2 0),1)) ∧
        (∀ u,edge u∈a.val.image →
          ∃ finalQ : C(Interval,range BC),(∀ t,(finalQ t).val=edge t) ∧
          (∀ v w,v<u → u<w →
            (hBC.toHomeomorph.symm (finalQ v)).2.val≠0 ∧
            (hBC.toHomeomorph.symm (finalQ w)).2.val≠0 ∧
            ((0<(hBC.toHomeomorph.symm (finalQ v)).2.val) ↔
              ¬(0<(hBC.toHomeomorph.symm (finalQ w)).2.val)))) := by
    let i := e.val.1
    let j := e.val.2
    let prev : Fin n := ⟨j.val-1,by omega⟩
    by_cases hs : label e.val=true ∧ label (i,prev)=true
    · obtain ⟨edge,H,hstart,hend,hends,hmarks,hHR,hER,hclear,hfinite,hunique,hinside,finalQ,hdecode,hflip⟩ :=
        actual_shared_horizontal_grid_edge_redraw_affine_in_range M a BC hBC hmarks haxis
          R n hn cell hcell label hrange hvertex i
          (⟨j.val,by omega⟩ : Fin (n+1)) ⟨e.property,j.isLt⟩ hs.1
      have hnode : actualHalfMeshParameter n hn ⟨2*j.val,by omega⟩=
          ArcFinitePosition.intervalMeshParameter n hn j 0 := by
        apply Subtype.ext
        change ((2*j.val:ℕ):ℝ)/(2*n)=((j.val:ℝ)+0)/n
        have hnR : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
        push_cast
        field_simp
        ring
      refine ⟨edge,H,?_,hend,?_,hmarks,(fun _ => hHR),hfinite,hunique,hinside,?_,?_⟩
      · simpa only [hnode] using hstart
      · simpa only [hnode] using hends
      · intro hf
        rcases hf with h | h
        · simp [hs.1] at h
        · change label (i,prev)=false at h
          cases hs.2.symm.trans h
      · intro u hu
        exact ⟨finalQ,hdecode,fun v w hv hw => hflip u v w hu hv hw⟩
    · have hf : label e.val=false ∨ label (i,prev)=false := by
        by_cases hu : label e.val=true
        · right
          have hv : label (i,prev)≠true := fun hv => hs ⟨hu,hv⟩
          cases h : label (i,prev)
          · rfl
          · exact False.elim (hv h)
        · left
          cases h : label e.val
          · rfl
          · exact False.elim (hu h)
      let edge : C(Interval,S) :=
        ⟨fun t => R ((ArcFinitePosition.intervalMeshParameter n hn i t,
          ArcFinitePosition.intervalMeshParameter n hn j 0),1),by
          exact R.continuous.comp
            (((ArcFinitePosition.intervalMeshParameter_continuous n hn i).prodMk
              continuous_const).prodMk continuous_const)⟩
      let H : C(Interval × Interval,S) := ⟨fun z => edge z.2,by fun_prop⟩
      have hfree (t) : edge t ∉ a.val.image :=
        actual_horizontal_off_interface_clear a.val.image R n hn label hoff i j e.property hf t 1
      have hempty : {t : Interval | edge t ∈ a.val.image}=∅ :=
        eq_empty_iff_forall_notMem.mpr hfree
      refine ⟨edge,H,(fun _ => rfl),(fun _ => rfl),(fun _ => ⟨rfl,rfl⟩),
        (fun z => hRmarks _),?_,?_,
        (fun t _ ht _ => False.elim (hfree t ht)),
        (fun t ht => False.elim (hfree t ht)),(fun _ _ _ => rfl),?_⟩
      · intro hu z
        apply hrange e.val hu _ _ 1
        rw [hcell e.val]
        exact ⟨(z.2,0),rfl⟩
      · rw [hempty]
        exact finite_empty
      · intro u hu
        exact False.elim (hfree u hu)
  choose edge H hH using hex
  exact ⟨edge,H,hH⟩
end CurveComplex.HyperellipticModel
