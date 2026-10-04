import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualClosingFramedMiddleBudget
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualFirstReturnAttachedCaps
namespace CurveComplex
open Set Topology Schoenflies
/-- Actual globally narrowed framed tracks, with caps on the one ambient
translated whole boundary. The middle budgets hold on closed source intervals. -/
structure SourceFirstReturnBudgetTracks
    {S : Type} [TopologicalSpace S] {a b : Curve S}
    (D : SourceFirstReturnBoundary a b) (B : SourceTwoSurgeryBranches D) (i : Bool) where
  F : SourceFirstReturnFramedStrips D B i
  caps : SourceFirstReturnAttachedCaps F
  first_middle : ∀ u ∈ Set.Icc (F.θf false) (F.θf true), ∀ w : Set.Icc (-1:ℝ) 1,
    F.N (u,w) ∉ b.image ∧ (F.N (u,w) ∈ a.image ↔ (w:ℝ)=0)
  closing_middle : ∀ u ∈ Set.Icc (F.θg false) (F.θg true), ∀ w : Set.Icc (-1:ℝ) 1,
    (F.M (u,w) ∈ b.image ↔ (w:ℝ)=0) ∧
    (F.M (u,w) ∈ a.image → ∃ p : source_surgery_retained_crossings B i, u=F.θR p)

theorem source_first_return_actual_budget_tracks
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    {a b : Curve S} (D : SourceFirstReturnBoundary a b)
    (B : SourceTwoSurgeryBranches D) (ht : Transverse a b) (i : Bool) :
    Nonempty (SourceFirstReturnBudgetTracks D B i) := by
  classical
  obtain ⟨F⟩ := source_first_return_whole_framed_strips S D B ht i
  obtain ⟨ρ,hρ,N,hN,hNformula,hNc,hNbudget⟩ := source_first_framed_middle_uniform_avoidance S D B i F
  obtain ⟨τ,hτ,M,hM,hMformula,hMc,hMbudget⟩ := source_closing_framed_middle_uniform_budget S D B ht i F
  let G : SourceFirstReturnFramedStrips D B i := {
    F with
    N:=N,M:=M,first_embedding:=hN,closing_embedding:=hM,first_center:=hNc,closing_center:=hMc,
    α:=fun k=>F.α k*ρ,β:=fun k=>F.β k*τ,γ:=fun p=>F.γ p*τ,
    corner_positive:=fun k=>⟨mul_ne_zero (F.corner_positive k).1 hρ.1.ne',
      mul_ne_zero (F.corner_positive k).2.1 hτ.1.ne',(F.corner_positive k).2.2⟩,
    retained_positive:=fun p=>⟨mul_ne_zero (F.retained_positive p).1 hτ.1.ne',(F.retained_positive p).2⟩,
    first_framing:=by
      intro k u w hu
      let w' : Set.Icc (-1:ℝ) 1 := ⟨ρ*(w:ℝ),by constructor <;> nlinarith [w.property.1,w.property.2,hρ.1,hρ.2]⟩
      have he : N (u,w)=F.N (u,w') := hNformula (u,w)
      obtain ⟨hs,hcoords⟩ := F.first_framing k u w' hu
      refine ⟨he ▸ hs,?_⟩
      rw [he,hcoords]
      ext j
      fin_cases j
      · change F.α k*(ρ*(w:ℝ))=F.α k*ρ*(w:ℝ); ring
      · rfl,
    closing_framing:=by
      intro k u w hu
      let w' : Set.Icc (-1:ℝ) 1 := ⟨τ*(w:ℝ),by constructor <;> nlinarith [w.property.1,w.property.2,hτ.1,hτ.2]⟩
      have he : M (u,w)=F.M (u,w') := hMformula (u,w)
      obtain ⟨hs,hcoords⟩ := F.closing_framing k u w' hu
      refine ⟨he ▸ hs,?_⟩
      rw [he,hcoords]
      ext j
      fin_cases j
      · rfl
      · change F.β k*(τ*(w:ℝ))=F.β k*τ*(w:ℝ); ring,
    retained_framing:=by
      intro p u w hu
      let w' : Set.Icc (-1:ℝ) 1 := ⟨τ*(w:ℝ),by constructor <;> nlinarith [w.property.1,w.property.2,hτ.1,hτ.2]⟩
      have he : M (u,w)=F.M (u,w') := hMformula (u,w)
      obtain ⟨hs,hcoords⟩ := F.retained_framing p u w' hu
      refine ⟨he ▸ hs,?_⟩
      rw [he,hcoords]
      ext j
      fin_cases j
      · rfl
      · change F.γ p*(τ*(w:ℝ))=F.γ p*τ*(w:ℝ); ring
  }
  obtain ⟨A⟩ := source_framed_first_return_caps_on_whole_curve S D B ht i G
  exact ⟨{F:=G,caps:=A,first_middle:=hNbudget,closing_middle:=hMbudget}⟩
end CurveComplex
#print axioms CurveComplex.source_first_return_actual_budget_tracks
