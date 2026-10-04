import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualUniformCellSharedBoundaryMovieGluing
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualHomotopyConcatenationAvoidance
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- The common schedule on the actual physical grid glues all three surface
stages jointly. The boundary assignment is the produced physical assignment;
its continuity is not needed, since the cell movies are continuous. -/
theorem actual_uniform_three_stage_surface_gluing
    {S : Type} [TopologicalSpace S]
    (n : ℕ) (hn : 0<n)
    (f0 f1 f2 f3 : (Fin n × Fin n) → C(Interval × Interval,S))
    (first : ∀ k,(f0 k).Homotopy (f1 k))
    (middle : ∀ k,(f1 k).Homotopy (f2 k))
    (last : ∀ k,(f2 k).Homotopy (f3 k))
    (B : ((Interval × Interval) × Interval) → S)
    (hfirst : ∀ k z σ,z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 →
      first k (σ,z)=B ((ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
        ArcFinitePosition.intervalMeshParameter n hn k.2 z.2),0))
    (hmiddle : ∀ k z σ,z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 →
      middle k (σ,z)=B ((ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
        ArcFinitePosition.intervalMeshParameter n hn k.2 z.2),σ))
    (hlast : ∀ k z σ,z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 →
      last k (σ,z)=B ((ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
        ArcFinitePosition.intervalMeshParameter n hn k.2 z.2),1))
    (forbidden : Set S)
    (havoid : ∀ k σ z,((first k |>.trans (middle k)).trans (last k)) (σ,z) ∉ forbidden) :
    ∃ R : C((Interval × Interval) × Interval,S),
      (∀ k z σ,R ((ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
        ArcFinitePosition.intervalMeshParameter n hn k.2 z.2),σ)=
          ((first k |>.trans (middle k)).trans (last k)) (σ,z)) ∧
      (∀ k z,R ((ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
        ArcFinitePosition.intervalMeshParameter n hn k.2 z.2),0)=f0 k z) ∧
      (∀ k z,R ((ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
        ArcFinitePosition.intervalMeshParameter n hn k.2 z.2),1)=f3 k z) ∧
      (∀ z,R z ∉ forbidden) := by
  let scheduled : ((Interval × Interval) × Interval) → S := fun q =>
    if h : (q.2:ℝ)≤1/2 then
      if h' : 2*(q.2:ℝ)≤1/2 then B (q.1,0)
      else B (q.1,⟨4*(q.2:ℝ)-1,by constructor <;> nlinarith⟩)
    else B (q.1,1)
  let movie (k : Fin n × Fin n) : C((Interval × Interval) × Interval,S) :=
    ⟨fun q => ((first k |>.trans (middle k)).trans (last k)) (q.2,q.1),
      (((first k |>.trans (middle k)).trans (last k)).continuous.comp
        (continuous_snd.prodMk continuous_fst))⟩
  have hb (k) (z : Interval × Interval) (σ : Interval)
      (hz : z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1) :
      movie k (z,σ)=scheduled ((ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
        ArcFinitePosition.intervalMeshParameter n hn k.2 z.2),σ) := by
    change ((first k |>.trans (middle k)).trans (last k)) (σ,z)=_
    rw [ContinuousMap.Homotopy.trans_apply]
    dsimp only [scheduled]
    by_cases hs : (σ:ℝ)≤1/2
    · rw [dite_eq_left hs,dite_eq_left hs]
      rw [ContinuousMap.Homotopy.trans_apply]
      dsimp only [Prod.fst,Prod.snd,Subtype.coe_mk]
      by_cases ht : 2*(σ:ℝ)≤1/2
      · rw [dite_eq_left ht,dite_eq_left ht]
        exact hfirst k z _ hz
      · rw [dite_eq_right ht,dite_eq_right ht,hmiddle k z _ hz]
        congr 2
        apply Subtype.ext
        change 2*(2*(σ:ℝ))-1=4*(σ:ℝ)-1
        ring
    · rw [dite_eq_right hs,dite_eq_right hs]
      exact hlast k z _ hz
  obtain ⟨R,hR⟩ := actual_uniform_cell_shared_boundary_movie_gluing scheduled n hn movie hb
  refine ⟨R,hR,?_,?_,?_⟩
  · intro k z
    rw [hR]
    exact ((first k |>.trans (middle k)).trans (last k)).map_zero_left z
  · intro k z
    rw [hR]
    exact ((first k |>.trans (middle k)).trans (last k)).map_one_left z
  · rintro ⟨z,σ⟩
    obtain ⟨i,s,hs⟩ := ArcFinitePosition.intervalMeshParameter_cover n hn z.1
    obtain ⟨j,t,ht⟩ := ArcFinitePosition.intervalMeshParameter_cover n hn z.2
    have he : (ArcFinitePosition.intervalMeshParameter n hn i s,
      ArcFinitePosition.intervalMeshParameter n hn j t)=z := Prod.ext hs ht
    rw [←he,hR (i,j) (s,t) σ]
    exact havoid (i,j) σ (s,t)
end CurveComplex.HyperellipticModel
