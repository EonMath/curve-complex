import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualRawCapRemoteSeparation
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualFirstReturnCapsWithRadius
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualFirstReturnDisjointMiddleBands
namespace CurveComplex
open Set Topology Schoenflies
/-- Actual uniform remote localization completes all FOUR global cap/middle
port incidences. The source construction retains disjoint whole middle bands
and all exact crossing budgets; no desired incidence is an input. -/
theorem source_first_return_global_port_incidence
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    {a b : Curve S} (D : SourceFirstReturnBoundary a b)
    (B : SourceTwoSurgeryBranches D) (ht : Transverse a b) (i : Bool) :
    ∃ P : SourceFirstReturnBudgetTracks D B i,
      Disjoint
        (P.F.N '' (Set.Icc (P.F.θf false) (P.F.θf true) ×ˢ (Set.univ : Set (Set.Icc (-1:ℝ) 1))))
        (P.F.M '' (Set.Icc (P.F.θg false) (P.F.θg true) ×ˢ (Set.univ : Set (Set.Icc (-1:ℝ) 1)))) ∧
      (∀ k u, u ∈ Set.Icc (P.F.θf false) (P.F.θf true) →
        (P.F.N (u,P.caps.w) ∈ Set.range (P.caps.C k) ↔ u=P.F.θf k)) ∧
      (∀ k u, u ∈ Set.Icc (P.F.θg false) (P.F.θg true) →
        (P.F.M (u,P.caps.z) ∈ Set.range (P.caps.C k) ↔ u=P.F.θg k)) := by
  classical
  obtain ⟨P,hPdis⟩ := source_first_return_actual_disjoint_budget_tracks S D B ht i
  let F := P.F
  obtain ⟨W,hW,hlegs,hfirstW,hclosingW,r,hr,hsmall⟩ := source_raw_caps_remote_middle_separation S D B i F
  have hCf (k) : IsClosed (source_first_middle_far_parameters F k) :=
    isClosed_Icc.inter (isClosed_le continuous_const (by fun_prop))
  have hCg (k) : IsClosed (source_closing_middle_far_parameters F k) :=
    isClosed_Icc.inter (isClosed_le continuous_const (by fun_prop))
  obtain ⟨ρ,hρ,N,hN,hNformula,hNc₀,hNW⟩ :=
    source_strip_finite_parameter_localization F.N F.first_embedding Bool
      (source_first_middle_far_parameters F) hCf (fun k=>(closure (W k))ᶜ)
      (fun _=>isClosed_closure.isOpen_compl) (by
        intro k u hu
        rw [F.first_center]
        exact hfirstW k u hu)
  obtain ⟨τ,hτ,M,hM,hMformula,hMc₀,hMW⟩ :=
    source_strip_finite_parameter_localization F.M F.closing_embedding Bool
      (source_closing_middle_far_parameters F) hCg (fun k=>(closure (W k))ᶜ)
      (fun _=>isClosed_closure.isOpen_compl) (by
        intro k u hu
        rw [F.closing_center]
        exact hclosingW k u hu)
  have hNc (u) : N (u,⟨0,by norm_num⟩)=D.first u := (hNc₀ u).trans (F.first_center u)
  have hMc (u) : M (u,⟨0,by norm_num⟩)=B.closing i u := (hMc₀ u).trans (F.closing_center u)
  have hNbudget : ∀ u ∈ Set.Icc (F.θf false) (F.θf true), ∀ w : Set.Icc (-1:ℝ) 1,
      N (u,w) ∉ b.image ∧ (N (u,w) ∈ a.image ↔ (w:ℝ)=0) := by
    intro u hu w
    let w' : Set.Icc (-1:ℝ) 1 := ⟨ρ*(w:ℝ),by constructor <;> nlinarith [w.property.1,w.property.2,hρ.1,hρ.2]⟩
    have he : N (u,w)=F.N (u,w') := hNformula (u,w)
    rw [he]
    obtain ⟨hb,ha⟩ := P.first_middle u hu w'
    refine ⟨hb,ha.trans ?_⟩
    change ρ*(w:ℝ)=0 ↔ (w:ℝ)=0
    exact mul_eq_zero_iff_left hρ.1.ne'
  have hMbudget : ∀ u ∈ Set.Icc (F.θg false) (F.θg true), ∀ w : Set.Icc (-1:ℝ) 1,
      (M (u,w) ∈ b.image ↔ (w:ℝ)=0) ∧
      (M (u,w) ∈ a.image → ∃ p : source_surgery_retained_crossings B i, u=F.θR p) := by
    intro u hu w
    let w' : Set.Icc (-1:ℝ) 1 := ⟨τ*(w:ℝ),by constructor <;> nlinarith [w.property.1,w.property.2,hτ.1,hτ.2]⟩
    have he : M (u,w)=F.M (u,w') := hMformula (u,w)
    rw [he]
    obtain ⟨hb,ha⟩ := P.closing_middle u hu w'
    refine ⟨hb.trans ?_,ha⟩
    change τ*(w:ℝ)=0 ↔ (w:ℝ)=0
    exact mul_eq_zero_iff_left hτ.1.ne'
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
  let rmax : ℝ := min (r false) (r true)
  obtain ⟨A,hAr⟩ := source_framed_first_return_caps_with_arbitrary_radius S D B ht i G rmax (lt_min (hr false) (hr true))
  have hAW (k) (x : S) (hx : x ∈ Set.range (A.C k)) : x ∈ W k := by
    have hrr : rmax≤r k := by cases k; exact min_le_left _ _; exact min_le_right _ _
    exact hsmall k (A.v k) ((hAr k).trans_le hrr) x (A.subset k hx).1
      (source_attached_cap_truncation_heights A k x hx)
  let Q : SourceFirstReturnBudgetTracks D B i := {
    F:=G,caps:=A,first_middle:=hNbudget,closing_middle:=hMbudget }
  have hNsub : N '' (Set.Icc (G.θf false) (G.θf true) ×ˢ (Set.univ : Set (Set.Icc (-1:ℝ) 1))) ⊆
      F.N '' (Set.Icc (F.θf false) (F.θf true) ×ˢ (Set.univ : Set (Set.Icc (-1:ℝ) 1))) := by
    rintro x ⟨⟨u,w⟩,hu,rfl⟩
    exact ⟨(u,⟨ρ*(w:ℝ),by constructor <;> nlinarith [w.property.1,w.property.2,hρ.1,hρ.2]⟩),
      ⟨hu.1,Set.mem_univ _⟩,(hNformula (u,w)).symm⟩
  have hMsub : M '' (Set.Icc (G.θg false) (G.θg true) ×ˢ (Set.univ : Set (Set.Icc (-1:ℝ) 1))) ⊆
      F.M '' (Set.Icc (F.θg false) (F.θg true) ×ˢ (Set.univ : Set (Set.Icc (-1:ℝ) 1))) := by
    rintro x ⟨⟨u,w⟩,hu,rfl⟩
    exact ⟨(u,⟨τ*(w:ℝ),by constructor <;> nlinarith [w.property.1,w.property.2,hτ.1,hτ.2]⟩),
      ⟨hu.1,Set.mem_univ _⟩,(hMformula (u,w)).symm⟩
  refine ⟨Q,hPdis.mono hNsub hMsub,?_,?_⟩
  · intro k u hu
    constructor
    · intro hx
      have hwindow : |(u:ℝ)-(G.θf k:ℝ)|<G.ηf k := by
        by_contra hn
        have hfar : u ∈ source_first_middle_far_parameters F k := ⟨hu,by
          have hh := le_of_not_gt hn
          have hpos := (F.corner_positive k).2.2.1
          change F.ηf k≤|(u:ℝ)-(F.θf k:ℝ)| at hh
          change F.ηf k/2≤|(u:ℝ)-(F.θf k:ℝ)|
          linarith⟩
        exact hNW k (u,A.w) hfar (subset_closure (hAW k _ hx))
      exact (source_attached_cap_first_middle_local_port A k u hu hwindow).mp hx
    · intro he
      rw [he,← A.first_port]
      exact Set.mem_range_self 0
  · intro k u hu
    constructor
    · intro hx
      have hwindow : |(u:ℝ)-(G.θg k:ℝ)|<G.ηg k := by
        by_contra hn
        have hfar : u ∈ source_closing_middle_far_parameters F k := ⟨hu,by
          have hh := le_of_not_gt hn
          have hpos := (F.corner_positive k).2.2.2
          change F.ηg k≤|(u:ℝ)-(F.θg k:ℝ)| at hh
          change F.ηg k/2≤|(u:ℝ)-(F.θg k:ℝ)|
          linarith⟩
        exact hMW k (u,A.z) hfar (subset_closure (hAW k _ hx))
      exact (source_attached_cap_closing_middle_local_port A k u hu hwindow).mp hx
    · intro he
      rw [he,← A.closing_port]
      exact Set.mem_range_self 1
end CurveComplex
#print axioms CurveComplex.source_first_return_global_port_incidence
