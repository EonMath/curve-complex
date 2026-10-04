import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualFirstFramedMiddleAvoidance
namespace CurveComplex
open Set Topology Schoenflies
/-- Uniformly narrow the actual closing whole framed strip. On the ENTIRE
closed middle interval, every target contact has one of the original retained
source parameters, and every nonzero track avoids the current curve. -/
theorem source_closing_framed_middle_uniform_budget
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    {a b : Curve S} (D : SourceFirstReturnBoundary a b)
    (B : SourceTwoSurgeryBranches D) (ht : Transverse a b) (i : Bool)
    (F : SourceFirstReturnFramedStrips D B i) :
    ∃ ρ : ℝ, ∃ hρ : 0<ρ ∧ ρ≤1,
      ∃ M : Interval × Set.Icc (-1:ℝ) 1 → S,
        IsEmbedding M ∧
        (∀ q, M q=F.M (q.1,⟨ρ*(q.2:ℝ),by
          constructor <;> nlinarith [q.2.property.1,q.2.property.2,hρ.1,hρ.2]⟩)) ∧
        (∀ u, M (u,⟨0,by norm_num⟩)=B.closing i u) ∧
        ∀ u ∈ Set.Icc (F.θg false) (F.θg true), ∀ w : Set.Icc (-1:ℝ) 1,
          (M (u,w) ∈ b.image ↔ (w:ℝ)=0) ∧
          (M (u,w) ∈ a.image → ∃ p : source_surgery_retained_crossings B i, u=F.θR p) := by
  classical
  let R := source_surgery_retained_crossings B i
  let : Fintype R := (source_surgery_closing_crossings_budget D B ht i).1.fintype
  let J := Set.Icc (F.θg false) (F.θg true)
  have hint (u : J) : 0<(u.val:ℝ) ∧ (u.val:ℝ)<1 :=
    ⟨lt_of_lt_of_le (F.θg_internal false).1 u.property.1,
      lt_of_le_of_lt u.property.2 (F.θg_internal true).2⟩
  have hclosing (u : Interval) : B.closing i u ∈ b.image := by
    rw [← B.closing_cover]
    cases i
    · exact Or.inl (Set.mem_range_self u)
    · exact Or.inr (Set.mem_range_self u)
  choose U hU hpU hUsub htrace using fun u : J =>
    source_subarc_internal_local_trace S b (B.closing i) (B.closing_embedded i)
      (by rintro x ⟨t,rfl⟩; exact hclosing t) u.val (hint u).1 (hint u).2
      Set.univ isOpen_univ (Set.mem_univ _)
  let V : Set S := ⋃ u : J, U u
  have hV : IsOpen V := isOpen_iUnion hU
  have hcenterV (u : Interval) (hu : u ∈ J) : F.M (u,⟨0,by norm_num⟩) ∈ V := by
    rw [F.closing_center]
    exact Set.mem_iUnion.mpr ⟨⟨u,hu⟩,hpU ⟨u,hu⟩⟩
  let Cgap : Set Interval := J ∩ ⋂ p : R, {u : Interval | F.ηR p/2≤|(u:ℝ)-(F.θR p:ℝ)|}
  have hCgap : IsClosed Cgap := isClosed_Icc.inter
    (isClosed_iInter (fun p=>isClosed_le continuous_const (by fun_prop)))
  have hgap (u : Interval) (hu : u ∈ Cgap) : B.closing i u ∉ a.image := by
    intro hxa
    have hu0 : u≠0 := by intro he; have hh : 0<(u:ℝ) := (hint ⟨u,hu.1⟩).1; rw [he] at hh; norm_num at hh
    have hu1 : u≠1 := by intro he; have hh : (u:ℝ)<1 := (hint ⟨u,hu.1⟩).2; rw [he] at hh; norm_num at hh
    have hpR : B.closing i u ∈ R := by
      refine ⟨⟨Set.mem_range_self u,hxa⟩,?_⟩
      rintro (hh|hh)
      · exact hu0 ((B.closing_embedded i).injective (hh.trans (B.closing_zero i).symm))
      · exact hu1 ((B.closing_embedded i).injective (hh.trans (B.closing_one i).symm))
    let p : R := ⟨B.closing i u,hpR⟩
    have huθ : u=F.θR p := (B.closing_embedded i).injective (F.θR_center p).symm
    have hh := Set.mem_iInter.mp hu.2 p
    change F.ηR p/2≤|(u:ℝ)-(F.θR p:ℝ)| at hh
    rw [huθ,sub_self,abs_zero] at hh
    linarith [(F.retained_positive p).2]
  let C : Bool → Set Interval := fun k=>if k then Cgap else J
  let W : Bool → Set S := fun k=>if k then a.imageᶜ else V
  obtain ⟨ρ,hρ,M,hM,hformula,hMc,hMW⟩ :=
    source_strip_finite_parameter_localization F.M F.closing_embedding Bool C
      (by intro k; cases k; exact isClosed_Icc; exact hCgap) W
      (by intro k; cases k; exact hV; exact (isCompact_range a.embedded.continuous).isClosed.isOpen_compl)
      (by
        intro k u hu
        cases k
        · exact hcenterV u hu
        · rw [F.closing_center]; exact hgap u hu)
  have hcenterM (u) : M (u,⟨0,by norm_num⟩)=B.closing i u := (hMc u).trans (F.closing_center u)
  refine ⟨ρ,hρ,M,hM,hformula,hcenterM,?_⟩
  intro u hu w
  have hxV : M (u,w) ∈ V := hMW false (u,w) hu
  obtain ⟨v,hxU⟩ := Set.mem_iUnion.mp hxV
  refine ⟨?_,?_⟩
  · constructor
    · intro hxb
      obtain ⟨t,ht⟩ := (htrace v _ hxU).mp hxb
      have he : (u,w)=(t,⟨0,by norm_num⟩) := hM.injective (ht.symm.trans (hcenterM t).symm)
      exact congrArg (fun q : Interval × Set.Icc (-1:ℝ) 1 => (q.2:ℝ)) he
    · intro hw
      have he : w=(⟨0,by norm_num⟩ : Set.Icc (-1:ℝ) 1) := Subtype.ext hw
      rw [he,hcenterM]
      exact hclosing u
  · intro hxa
    have hnear : ∃ p : R, |(u:ℝ)-(F.θR p:ℝ)|<F.ηR p/2 := by
      by_contra hn
      push Not at hn
      have hh := hMW true (u,w) (show u ∈ Cgap from ⟨hu,Set.mem_iInter.mpr hn⟩)
      exact hh hxa
    obtain ⟨p,hup⟩ := hnear
    have huη : |(u:ℝ)-(F.θR p:ℝ)|<F.ηR p := by linarith [(F.retained_positive p).2]
    let w' : Set.Icc (-1:ℝ) 1 := ⟨ρ*(w:ℝ),by
      constructor <;> nlinarith [w.property.1,w.property.2,hρ.1,hρ.2]⟩
    have hsmall : M (u,w)=F.M (u,w') := hformula (u,w)
    obtain ⟨hxE,hEx⟩ := F.retained_framing p u w' huη
    have hx0 : F.ER p (F.M (u,w')) 0=0 := (F.retained_target_axis p _ hxE).mp (hsmall ▸ hxa)
    have huE := (F.retained_framing p u ⟨0,by norm_num⟩ huη).1
    rw [F.closing_center] at huE
    have huaxis := (F.retained_current_axis p _ huE).mp (hclosing u)
    have huc0 : F.ER p (B.closing i u) 0=0 := by
      have hh := congrArg (fun q : Plane=>q 0) hEx
      change F.ER p (F.M (u,w')) 0=F.ER p (B.closing i u) 0 at hh
      exact hh.symm.trans hx0
    have heE : F.ER p (B.closing i u)=F.ER p p.val := by
      rw [(F.retained_point p).2]
      ext j
      fin_cases j
      · exact huc0
      · exact huaxis
    have huc : B.closing i u=p.val := (F.ER p).injOn huE (F.retained_point p).1 heE
    exact ⟨p,(B.closing_embedded i).injective (huc.trans (F.θR_center p).symm)⟩
end CurveComplex
#print axioms CurveComplex.source_closing_framed_middle_uniform_budget
