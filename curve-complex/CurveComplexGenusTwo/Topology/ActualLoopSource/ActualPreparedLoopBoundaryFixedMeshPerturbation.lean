import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualClosedSupportMovieGluing
namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- Actual source-only supported movie preparation: all four literal sides and
all marked-point avoidance are preserved, and the selected mesh centres become
old-arc-free. This is a preparation, not the final finite contact drawing. -/
theorem actual_prepared_loop_boundary_fixed_mesh_perturbation
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
    ∃ n : ℕ, ∃ hn : 0<n, ∃ label : (Fin n × Fin n) → Bool,
    ∃ point : {k : Fin n × Fin n // label k=true} → T,
      (∀ k,(point k).val=
        (ArcFinitePosition.intervalMeshParameter n hn k.val.1 ⟨1/2,by norm_num⟩,
         ArcFinitePosition.intervalMeshParameter n hn k.val.2 ⟨1/2,by norm_num⟩)) ∧
    ∃ R : C((Interval × Interval) × Interval,S),
      (∀ z,R (z,0)=G z) ∧
      (∀ z σ,z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 → R (z,σ)=G z) ∧
      (∀ z,R z ∉ (M.cover.branch : Set S)) ∧
      (∀ k,R ((point k).val,1) ∉ a.val.image) := by
  classical
  obtain ⟨n,hn,label,point,hpoint,support,hclosed,hST,hcontactsSupport,
    δ,weight,hδ,hweight,hoff,hboundary,hclear,hbound⟩ :=
    actual_prepared_loop_mesh_center_perturbation M a G T hT hcontacts ψ
      (fun z => (hψbounds z).2) hψzero
  have hupper (z : T) : ψ z+δ*weight z.val<1 := by
    by_cases hz : z.val ∈ support
    · exact hbound z.val hz
    · simpa only [hoff z.val hz,mul_zero,add_zero] using (hψbounds z).2
  obtain ⟨J,hJstart,hJfixed,hJmarks,hJcoord⟩ :=
    actual_common_strip_normal_shift_movie M G T BC hBC hBCmarks Q hQ ψ hψ
      hψbounds weight (fun z => (hweight z).1) δ hδ.le hupper
  obtain ⟨R,hRlocal,hRoff⟩ := actual_closed_support_movie_gluing G T support hT hclosed hST J
    (fun z σ hz => hJfixed z σ (hoff z.val hz))
  refine ⟨n,hn,label,point,hpoint,R,?_,?_,?_,?_⟩
  · intro z
    by_cases hz : z ∈ T
    · exact (hRlocal ⟨z,hz⟩ 0).trans (hJstart ⟨z,hz⟩)
    · exact hRoff z 0 (fun hs => hz (hST hs))
  · intro z σ hb
    by_cases hz : z ∈ T
    · exact (hRlocal ⟨z,hz⟩ σ).trans (hJfixed ⟨z,hz⟩ σ (hboundary z hb))
    · exact hRoff z σ (fun hs => hz (hST hs))
  · intro z
    by_cases hz : z.1 ∈ T
    · rw [hRlocal ⟨z.1,hz⟩ z.2]
      exact hJmarks (⟨z.1,hz⟩,z.2)
    · rw [hRoff z.1 z.2 (fun hs => hz (hST hs))]
      exact hmarks z.1
  · intro k hk
    rw [hRlocal (point k) 1,hJcoord] at hk
    have hh := (hBCaxis _).mp hk
    change ψ (point k)+1*δ*weight (point k).val=0 at hh
    simp only [one_mul] at hh
    exact hclear k hh
end CurveComplex.HyperellipticModel
