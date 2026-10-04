import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualFirstReturnWholeTraceBudget
namespace CurveComplex
open Set Topology Schoenflies
/-- Separate the ENTIRE first and closing middle bands by a uniform narrowing
of the closing strip. This uses actual compact band images and the already
produced whole-middle current avoidance, rather than assuming disjoint tracks. -/
theorem source_budget_tracks_disjoint_middle_bands
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    {a b : Curve S} (D : SourceFirstReturnBoundary a b)
    (B : SourceTwoSurgeryBranches D) (ht : Transverse a b) (i : Bool)
    (P : SourceFirstReturnBudgetTracks D B i) :
    ∃ Q : SourceFirstReturnBudgetTracks D B i,
      Disjoint
        (Q.F.N '' (Set.Icc (Q.F.θf false) (Q.F.θf true) ×ˢ (Set.univ : Set (Set.Icc (-1:ℝ) 1))))
        (Q.F.M '' (Set.Icc (Q.F.θg false) (Q.F.θg true) ×ˢ (Set.univ : Set (Set.Icc (-1:ℝ) 1)))) := by
  classical
  let T := P.F.N '' (Set.Icc (P.F.θf false) (P.F.θf true) ×ˢ (Set.univ : Set (Set.Icc (-1:ℝ) 1)))
  have hTc : IsCompact T := (isCompact_Icc.prod isCompact_univ).image P.F.first_embedding.continuous
  have hTb : Disjoint T b.image := Set.disjoint_left.mpr (by
    rintro x ⟨⟨u,w⟩,hu,rfl⟩ hx
    exact (P.first_middle u hu.1 w).1 hx)
  have hcenter (u : Interval) (_hu : u ∈ Set.Icc (P.F.θg false) (P.F.θg true)) :
      P.F.M (u,⟨0,by norm_num⟩) ∉ T := by
    rw [P.F.closing_center]
    intro hxT
    have hb : B.closing i u ∈ b.image := by
      rw [← B.closing_cover]
      cases i
      · exact Or.inl (Set.mem_range_self u)
      · exact Or.inr (Set.mem_range_self u)
    exact Set.disjoint_left.mp hTb hxT hb
  obtain ⟨τ,hτ,M,hM,hformula,hMc,hMT⟩ :=
    source_strip_finite_parameter_localization P.F.M P.F.closing_embedding Unit
      (fun _=>Set.Icc (P.F.θg false) (P.F.θg true)) (fun _=>isClosed_Icc)
      (fun _=>Tᶜ) (fun _=>hTc.isClosed.isOpen_compl) (fun _=>hcenter)
  let G : SourceFirstReturnFramedStrips D B i := {
    (P.F) with
    M:=M,closing_embedding:=hM,
    closing_center:=(fun u=>(hMc u).trans (P.F.closing_center u)),
    β:=fun k=>P.F.β k*τ,γ:=fun p=>P.F.γ p*τ,
    corner_positive:=fun k=>⟨(P.F.corner_positive k).1,
      mul_ne_zero (P.F.corner_positive k).2.1 hτ.1.ne',(P.F.corner_positive k).2.2⟩,
    retained_positive:=fun p=>⟨mul_ne_zero (P.F.retained_positive p).1 hτ.1.ne',(P.F.retained_positive p).2⟩,
    closing_framing:=by
      intro k u w hu
      let w' : Set.Icc (-1:ℝ) 1 := ⟨τ*(w:ℝ),by constructor <;> nlinarith [w.property.1,w.property.2,hτ.1,hτ.2]⟩
      have he : M (u,w)=P.F.M (u,w') := hformula (u,w)
      obtain ⟨hs,hcoords⟩ := P.F.closing_framing k u w' hu
      refine ⟨he ▸ hs,?_⟩
      rw [he,hcoords]
      ext j
      fin_cases j
      · rfl
      · change P.F.β k*(τ*(w:ℝ))=P.F.β k*τ*(w:ℝ); ring,
    retained_framing:=by
      intro p u w hu
      let w' : Set.Icc (-1:ℝ) 1 := ⟨τ*(w:ℝ),by constructor <;> nlinarith [w.property.1,w.property.2,hτ.1,hτ.2]⟩
      have he : M (u,w)=P.F.M (u,w') := hformula (u,w)
      obtain ⟨hs,hcoords⟩ := P.F.retained_framing p u w' hu
      refine ⟨he ▸ hs,?_⟩
      rw [he,hcoords]
      ext j
      fin_cases j
      · rfl
      · change P.F.γ p*(τ*(w:ℝ))=P.F.γ p*τ*(w:ℝ); ring
  }
  have hbudget : ∀ u ∈ Set.Icc (G.θg false) (G.θg true), ∀ w : Set.Icc (-1:ℝ) 1,
      (G.M (u,w) ∈ b.image ↔ (w:ℝ)=0) ∧
      (G.M (u,w) ∈ a.image → ∃ p : source_surgery_retained_crossings B i, u=G.θR p) := by
    intro u hu w
    let w' : Set.Icc (-1:ℝ) 1 := ⟨τ*(w:ℝ),by constructor <;> nlinarith [w.property.1,w.property.2,hτ.1,hτ.2]⟩
    have he : G.M (u,w)=P.F.M (u,w') := hformula (u,w)
    rw [he]
    obtain ⟨hb,ha⟩ := P.closing_middle u hu w'
    refine ⟨hb.trans ?_,ha⟩
    change τ*(w:ℝ)=0 ↔ (w:ℝ)=0
    exact mul_eq_zero_iff_left hτ.1.ne'
  obtain ⟨A⟩ := source_framed_first_return_caps_on_whole_curve S D B ht i G
  let Q : SourceFirstReturnBudgetTracks D B i := {
    F:=G,caps:=A,first_middle:=P.first_middle,closing_middle:=hbudget }
  refine ⟨Q,Set.disjoint_left.mpr ?_⟩
  rintro x hxT ⟨⟨u,w⟩,hu,rfl⟩
  exact hMT () (u,w) hu.1 hxT

theorem source_first_return_actual_disjoint_budget_tracks
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    {a b : Curve S} (D : SourceFirstReturnBoundary a b)
    (B : SourceTwoSurgeryBranches D) (ht : Transverse a b) (i : Bool) :
    ∃ P : SourceFirstReturnBudgetTracks D B i,
      Disjoint
        (P.F.N '' (Set.Icc (P.F.θf false) (P.F.θf true) ×ˢ (Set.univ : Set (Set.Icc (-1:ℝ) 1))))
        (P.F.M '' (Set.Icc (P.F.θg false) (P.F.θg true) ×ˢ (Set.univ : Set (Set.Icc (-1:ℝ) 1)))) := by
  obtain ⟨P⟩ := source_first_return_actual_budget_tracks S D B ht i
  exact source_budget_tracks_disjoint_middle_bands S D B ht i P
end CurveComplex
#print axioms CurveComplex.source_budget_tracks_disjoint_middle_bands
#print axioms CurveComplex.source_first_return_actual_disjoint_budget_tracks
