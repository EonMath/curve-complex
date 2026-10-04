import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualPreparedLoopWholeHalfMeshShift
namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- Actual preparation of all mesh vertices and poles simultaneously. Off cells
remain the literal original movie at every time, and all four sides are fixed. -/
theorem actual_prepared_loop_whole_mesh_movie_preparation
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (G : C(Interval × Interval,S)) (hmarks : ∀ z,G z ∉ (M.cover.branch : Set S))
    (BC : Interval × Icc (-1:ℝ) 1 → S) (hBC : IsEmbedding BC)
    (hBCmarks : ∀ z,BC z ∉ (M.cover.branch : Set S))
    (hBCaxis : ∀ z,BC z ∈ a.val.image ↔ z.2.val=0)
    (T : Set (Interval × Interval)) (hT : IsOpen T) (hcontacts : G ⁻¹' a.val.image ⊆ T)
    (Q : C(T,range BC)) (hQ : ∀ z : T,(Q z).val=G z.val)
    (ψ : C(T,ℝ)) (hψ : ∀ z : T,ψ z=((hBC.toHomeomorph.symm (Q z)).2:ℝ))
    (hψbounds : ∀ z : T,-1<ψ z ∧ ψ z<1)
    (hψzero : ∀ z : T,ψ z=0 ↔ G z.val ∈ a.val.image) :
    ∃ n : ℕ, ∃ hn : 0<n,
    ∃ cell : (Fin n × Fin n) → Set (Interval × Interval),
      (∀ k,cell k=range (fun z : Interval × Interval =>
        (ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
          ArcFinitePosition.intervalMeshParameter n hn k.2 z.2))) ∧
      (∀ k,IsClosed (cell k)) ∧ (∀ z,∃ k,z ∈ cell k) ∧
    ∃ label : (Fin n × Fin n) → Bool,
      (∀ k,label k=true → cell k ⊆ T) ∧
      (∀ k,label k=false → ∀ z ∈ cell k,G z ∉ a.val.image) ∧
    ∃ R : C((Interval × Interval) × Interval,S),
      (∀ z,R (z,0)=G z) ∧
      (∀ z σ,z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 → R (z,σ)=G z) ∧
      (∀ z,R z ∉ (M.cover.branch : Set S)) ∧
      (∀ k,label k=true → ∀ z ∈ cell k,∀ σ,R (z,σ) ∈ range BC) ∧
      (∀ z σ,R (z,σ) ∈ a.val.image → z ∈ T) ∧
      (∀ k,label k=false → ∀ z ∈ cell k,∀ σ,R (z,σ)=G z) ∧
      (∀ i j : Fin (2*n+1),
        0<(actualHalfMeshParameter n hn i:ℝ) → (actualHalfMeshParameter n hn i:ℝ)<1 →
        0<(actualHalfMeshParameter n hn j:ℝ) → (actualHalfMeshParameter n hn j:ℝ)<1 →
        R ((actualHalfMeshParameter n hn i,actualHalfMeshParameter n hn j),1) ∉ a.val.image) := by
  classical
  obtain ⟨n,hn,cell,hcell,hclosed,hcover,label,hcellT,hcellOff,
    support,hsupportClosed,hsupportT,hcontactsSupport,
    δ,weight,hδ,hweight,hoff,hfalse,hboundary,hclear,hbound⟩ :=
    actual_prepared_loop_whole_half_mesh_shift M a G T hT hcontacts ψ
      (fun z => (hψbounds z).2) hψzero
  have hupper (z : T) : ψ z+δ*weight z.val<1 := by
    by_cases hz : z.val ∈ support
    · exact hbound z.val hz
    · simpa only [hoff z.val hz,mul_zero,add_zero] using (hψbounds z).2
  obtain ⟨J,hJstart,hJfixed,hJmarks,hJcoord⟩ :=
    actual_common_strip_normal_shift_movie M G T BC hBC hBCmarks Q hQ ψ hψ
      hψbounds weight (fun z => (hweight z).1) δ hδ.le hupper
  obtain ⟨R,hRlocal,hRoff⟩ := actual_closed_support_movie_gluing G T support hT hsupportClosed hsupportT J
    (fun z σ hz => hJfixed z σ (hoff z.val hz))
  refine ⟨n,hn,cell,hcell,hclosed,hcover,label,hcellT,hcellOff,R,?_,?_,?_,?_,?_,?_,?_⟩
  · intro z
    by_cases hz : z ∈ T
    · exact (hRlocal ⟨z,hz⟩ 0).trans (hJstart ⟨z,hz⟩)
    · exact hRoff z 0 (fun hs => hz (hsupportT hs))
  · intro z σ hb
    by_cases hz : z ∈ T
    · exact (hRlocal ⟨z,hz⟩ σ).trans (hJfixed ⟨z,hz⟩ σ (hboundary z hb))
    · exact hRoff z σ (fun hs => hz (hsupportT hs))
  · intro z
    by_cases hz : z.1 ∈ T
    · rw [hRlocal ⟨z.1,hz⟩ z.2]
      exact hJmarks (⟨z.1,hz⟩,z.2)
    · rw [hRoff z.1 z.2 (fun hs => hz (hsupportT hs))]
      exact hmarks z.1
  · intro k hk z hz σ
    rw [hRlocal ⟨z,hcellT k hk hz⟩ σ,hJcoord]
    exact mem_range_self _
  · intro z σ hk
    by_contra hz
    rw [hRoff z σ (fun hs => hz (hsupportT hs))] at hk
    exact hz (hcontacts hk)
  · intro k hk z hz σ
    by_cases ht : z ∈ T
    · exact (hRlocal ⟨z,ht⟩ σ).trans (hJfixed ⟨z,ht⟩ σ (hfalse k hk z hz))
    · exact hRoff z σ (fun hs => ht (hsupportT hs))
  · intro i j hi0 hi1 hj0 hj1 hk
    by_cases hz : (actualHalfMeshParameter n hn i,actualHalfMeshParameter n hn j) ∈ T
    · rw [hRlocal ⟨_,hz⟩ 1,hJcoord] at hk
      have hh := (hBCaxis _).mp hk
      change ψ ⟨_,hz⟩+1*δ*weight (actualHalfMeshParameter n hn i,actualHalfMeshParameter n hn j)=0 at hh
      simp only [one_mul] at hh
      exact hclear i j hz hi0 hi1 hj0 hj1 hh
    · rw [hRoff _ 1 (fun hs => hz (hsupportT hs))] at hk
      exact hz (hcontacts hk)
end CurveComplex.HyperellipticModel
