import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualFirstReturnInteriorFramingInput
import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualFiniteInteriorAxisFraming
set_option maxHeartbeats 3000000
namespace CurveComplex
open Set Topology Schoenflies
/-- Actual whole source strips, simultaneously calibrated at the two corner
ports and every retained crossing. All centers are strictly internal source
parameters produced from the first-return dictionary. -/
structure SourceFirstReturnFramedStrips
    {S : Type} [TopologicalSpace S] {a b : Curve S}
    (D : SourceFirstReturnBoundary a b) (B : SourceTwoSurgeryBranches D) (i : Bool) where
  E : Bool → OpenPartialHomeomorph S Plane
  point : ∀ k, (if k then D.finish else D.start) ∈ (E k).source ∧ E k (if k then D.finish else D.start)=0
  square : ∀ k, Plane.closedSquare 0 1 ⊆ (E k).target
  disjoint : Disjoint (closure (E false).source) (closure (E true).source)
  retained_disjoint : ∀ k, Disjoint (closure (E k).source) (source_surgery_retained_crossings B i)
  target_axis : ∀ k x, x ∈ (E k).source → (x ∈ a.image ↔ E k x 0=0)
  current_axis : ∀ k x, x ∈ (E k).source → (x ∈ b.image ↔ E k x 1=0)
  branch_trace : ∀ k x, x ∈ (E k).source → (x ∈ (B.boundary i).image ↔
    (E k x 0=0 ∧ 0≤E k x 1) ∨ (0≤E k x 0 ∧ E k x 1=0))
  θf : Bool → Interval
  θg : Bool → Interval
  θf_internal : ∀ k, 0<(θf k:ℝ) ∧ (θf k:ℝ)<1
  θg_internal : ∀ k, 0<(θg k:ℝ) ∧ (θg k:ℝ)<1
  first_ports_order : (θf false:ℝ)<θf true
  closing_ports_order : (θg false:ℝ)<θg true
  first_height : ∀ k, 0<E k (D.first (θf k)) 1 ∧ E k (D.first (θf k)) 1≤1/8
  closing_height : ∀ k, 0<E k (B.closing i (θg k)) 0 ∧ E k (B.closing i (θg k)) 0≤1/8
  ER : source_surgery_retained_crossings B i → OpenPartialHomeomorph S Plane
  retained_point : ∀ p, p.val ∈ (ER p).source ∧ ER p p.val=0
  retained_square : ∀ p, Plane.closedSquare 0 1 ⊆ (ER p).target
  retained_target_axis : ∀ p x, x ∈ (ER p).source → (x ∈ a.image ↔ ER p x 0=0)
  retained_current_axis : ∀ p x, x ∈ (ER p).source → (x ∈ b.image ↔ ER p x 1=0)
  θR : source_surgery_retained_crossings B i → Interval
  θR_injective : Function.Injective θR
  θR_center : ∀ p, B.closing i (θR p)=p.val
  θR_internal : ∀ p, 0<(θR p:ℝ) ∧ (θR p:ℝ)<1
  N : Interval × Set.Icc (-1:ℝ) 1 → S
  M : Interval × Set.Icc (-1:ℝ) 1 → S
  first_embedding : IsEmbedding N
  closing_embedding : IsEmbedding M
  first_center : ∀ u, N (u,⟨0,by norm_num⟩)=D.first u
  closing_center : ∀ u, M (u,⟨0,by norm_num⟩)=B.closing i u
  α : Bool → ℝ
  β : Bool → ℝ
  ηf : Bool → ℝ
  ηg : Bool → ℝ
  corner_positive : ∀ k, α k≠0 ∧ β k≠0 ∧ 0<ηf k ∧ 0<ηg k
  first_framing : ∀ k (u : Interval) (w : Set.Icc (-1:ℝ) 1), |(u:ℝ)-(θf k:ℝ)|<ηf k →
    N (u,w) ∈ (E k).source ∧ E k (N (u,w))=Plane.mk (α k*(w:ℝ)) (E k (D.first u) 1)
  closing_framing : ∀ k (u : Interval) (w : Set.Icc (-1:ℝ) 1), |(u:ℝ)-(θg k:ℝ)|<ηg k →
    M (u,w) ∈ (E k).source ∧ E k (M (u,w))=Plane.mk (E k (B.closing i u) 0) (β k*(w:ℝ))
  γ : source_surgery_retained_crossings B i → ℝ
  ηR : source_surgery_retained_crossings B i → ℝ
  retained_positive : ∀ p, γ p≠0 ∧ 0<ηR p
  retained_framing : ∀ p (u : Interval) (w : Set.Icc (-1:ℝ) 1), |(u:ℝ)-(θR p:ℝ)|<ηR p →
    M (u,w) ∈ (ER p).source ∧ ER p (M (u,w))=Plane.mk (ER p (B.closing i u) 0) (γ p*(w:ℝ))

theorem source_first_return_whole_framed_strips
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    {a b : Curve S} (D : SourceFirstReturnBoundary a b)
    (B : SourceTwoSurgeryBranches D) (ht : Transverse a b) (i : Bool) :
    Nonempty (SourceFirstReturnFramedStrips D B i) := by
  classical
  obtain ⟨E,hpoint,hsquare,hdis,hER,ha,hb,hraw,θf,θg,hfi,hgi,hfint,hgint,
    hfl,hfr,hgl,hgr,hheightf,hheightg,F,G,hFGs,hFp,hGp,hFaxis,hGaxis,hFcoords,hGcoords⟩ :=
    source_first_return_interior_corner_framing_input S D B ht i
  obtain ⟨θR,hRi,hRc,hRint⟩ := source_retained_closing_framing_parameters D B i
  obtain ⟨ER,hRp,hRs,hRdis,hRfirst,hRother,hRa,hRb,hRraw⟩ :=
    source_retained_branch_square_charts D B ht i
  let R := source_surgery_retained_crossings B i
  let : Fintype R := (source_surgery_closing_crossings_budget D B ht i).1.fintype
  let θ : Bool ⊕ R → Interval := Sum.elim θg θR
  let Q : Bool ⊕ R → OpenPartialHomeomorph S Plane := Sum.elim G ER
  have hnotR (k : Bool) (p : R) : θg k ≠ θR p := by
    intro he
    have hp : p.val ∈ (E k).source := by
      rw [← hRc p,← he]
      exact (hFGs k).2 ▸ (hGp k).1
    exact Set.disjoint_left.mp (hER k) (subset_closure hp) p.property
  have hθ : Function.Injective θ := by
    intro k l he
    cases k with
    | inl k =>
      cases l with
      | inl l => exact congrArg Sum.inl (hgi he)
      | inr l => exact False.elim (hnotR k l he)
    | inr k =>
      cases l with
      | inl l => exact False.elim (hnotR l k he.symm)
      | inr l => exact congrArg Sum.inr (hRi he)
  have hpQ (k) : B.closing i (θ k) ∈ (Q k).source := by
    cases k with
    | inl k => exact (hGp k).1
    | inr p => change B.closing i (θR p) ∈ (ER p).source; rw [hRc]; exact (hRp p).1
  have hzQ (k) : Q k (B.closing i (θ k))=0 := by
    cases k with
    | inl k => exact (hGp k).2
    | inr p => change ER p (B.closing i (θR p))=0; rw [hRc]; exact (hRp p).2
  have haxisQ (k) (u : Interval) (hu : B.closing i u ∈ (Q k).source) : Q k (B.closing i u) 1=0 := by
    cases k with
    | inl k => exact hGaxis k u hu
    | inr p =>
      exact (hRb p _ hu).mp (by
        rw [← B.closing_cover]
        cases i
        · exact Or.inl (Set.mem_range_self u)
        · exact Or.inr (Set.mem_range_self u))
  obtain ⟨N,hN,hNU,hNc,σf,δf,ηf,hsf,hdf,hNcoords⟩ :=
    source_finite_interior_axis_framed_arc_strip S D.first D.first_embedded Bool θf hfi hfint F
      (fun k => (hFp k).1) (fun k => (hFp k).2) hFaxis Set.univ isOpen_univ (by simp)
  obtain ⟨M,hM,hMU,hMc,σg,δg,ηg,hsg,hdg,hMcoords⟩ :=
    source_finite_interior_axis_framed_arc_strip S (B.closing i) (B.closing_embedded i)
      (Bool ⊕ R) θ hθ (by intro k; cases k with | inl k => exact hgint k | inr p => exact hRint p)
      Q hpQ hzQ haxisQ Set.univ isOpen_univ (by simp)
  have hfnon (k) : σf k*δf k≠0 := by
    rcases hsf k with hh|hh <;> rw [hh] <;> exact mul_ne_zero (by norm_num) (ne_of_gt (hdf k).1)
  have hgnon (k) : σg k*δg k≠0 := by
    rcases hsg k with hh|hh <;> rw [hh] <;> exact mul_ne_zero (by norm_num) (ne_of_gt (hdg k).1)
  refine ⟨{
    E:=E,point:=hpoint,square:=hsquare,disjoint:=hdis,retained_disjoint:=hER,
    target_axis:=ha,current_axis:=hb,branch_trace:=hraw,
    θf:=θf,θg:=θg,θf_internal:=hfint,θg_internal:=hgint,
    first_ports_order:=by linarith,closing_ports_order:=by linarith,
    first_height:=hheightf,closing_height:=hheightg,
    ER:=ER,retained_point:=hRp,retained_square:=hRs,
    retained_target_axis:=hRa,retained_current_axis:=hRb,
    θR:=θR,θR_injective:=hRi,θR_center:=hRc,θR_internal:=hRint,
    N:=N,M:=M,first_embedding:=hN,closing_embedding:=hM,first_center:=hNc,closing_center:=hMc,
    α:=fun k=>σf k*δf k,β:=fun k=>σg (Sum.inl k)*δg (Sum.inl k),
    ηf:=ηf,ηg:=fun k=>ηg (Sum.inl k),
    corner_positive:=fun k=>⟨hfnon k,hgnon (Sum.inl k),(hdf k).2,(hdg (Sum.inl k)).2⟩,
    first_framing:=?_,closing_framing:=?_,
    γ:=fun p=>σg (Sum.inr p)*δg (Sum.inr p),ηR:=fun p=>ηg (Sum.inr p),
    retained_positive:=fun p=>⟨hgnon (Sum.inr p),(hdg (Sum.inr p)).2⟩,
    retained_framing:=fun p u w hu=>hMcoords (Sum.inr p) u w hu
  }⟩
  · intro k u w hu
    obtain ⟨hp,hcoord⟩ := hNcoords k u w hu
    refine ⟨(hFGs k).1 ▸ hp,?_⟩
    have h0 := congrArg (fun p : Plane => p 0) hcoord
    have h1 := congrArg (fun p : Plane => p 1) hcoord
    rw [hFcoords,hFcoords] at h0
    rw [hFcoords] at h1
    ext j
    fin_cases j
    · simpa using h1
    · change E k (N (u,w)) 1 - E k (D.first (θf k)) 1 =
        E k (D.first u) 1 - E k (D.first (θf k)) 1 at h0
      change E k (N (u,w)) 1 = E k (D.first u) 1
      linarith
  · intro k u w hu
    obtain ⟨hp,hcoord⟩ := hMcoords (Sum.inl k) u w hu
    refine ⟨(hFGs k).2 ▸ hp,?_⟩
    change G k (M (u,w))=Plane.mk (G k (B.closing i u) 0) (σg (Sum.inl k)*δg (Sum.inl k)*(w:ℝ)) at hcoord
    have h0 := congrArg (fun p : Plane => p 0) hcoord
    have h1 := congrArg (fun p : Plane => p 1) hcoord
    rw [hGcoords,hGcoords] at h0
    rw [hGcoords] at h1
    ext j
    fin_cases j
    · change E k (M (u,w)) 0 - E k (B.closing i (θg k)) 0 =
        E k (B.closing i u) 0 - E k (B.closing i (θg k)) 0 at h0
      change E k (M (u,w)) 0 = E k (B.closing i u) 0
      linarith
    · simpa using h1
end CurveComplex
#print axioms CurveComplex.source_first_return_whole_framed_strips
