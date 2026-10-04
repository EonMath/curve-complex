import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualFirstReturnFramedStrips
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualSubarcLocalTrace
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualFiniteStripLocalization
namespace CurveComplex
open Set Topology Schoenflies
/-- Uniformly narrow the actual first whole framed strip along the entire
closed interval between the selected ports. Its nonzero tracks avoid BOTH
old curves throughout this middle interval, rather than only pointwise near
the corners. The one global factor preserves every existing frame equation. -/
theorem source_first_framed_middle_uniform_avoidance
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    {a b : Curve S} (D : SourceFirstReturnBoundary a b)
    (B : SourceTwoSurgeryBranches D) (i : Bool)
    (F : SourceFirstReturnFramedStrips D B i) :
    ∃ ρ : ℝ, ∃ hρ : 0<ρ ∧ ρ≤1,
      ∃ N : Interval × Set.Icc (-1:ℝ) 1 → S,
        IsEmbedding N ∧
        (∀ q, N q=F.N (q.1,⟨ρ*(q.2:ℝ),by
          constructor <;> nlinarith [q.2.property.1,q.2.property.2,hρ.1,hρ.2]⟩)) ∧
        (∀ u, N (u,⟨0,by norm_num⟩)=D.first u) ∧
        ∀ u ∈ Set.Icc (F.θf false) (F.θf true), ∀ w : Set.Icc (-1:ℝ) 1,
          N (u,w) ∉ b.image ∧ (N (u,w) ∈ a.image ↔ (w:ℝ)=0) := by
  classical
  let J := Set.Icc (F.θf false) (F.θf true)
  have hint (u : J) : 0<(u.val:ℝ) ∧ (u.val:ℝ)<1 :=
    ⟨lt_of_lt_of_le (F.θf_internal false).1 u.property.1,
      lt_of_le_of_lt u.property.2 (F.θf_internal true).2⟩
  have hnotb (u : J) : D.first u.val ∉ b.image :=
    D.first_interior_avoids u.val
      (by intro he; have hh := (hint u).1; rw [he] at hh; norm_num at hh)
      (by intro he; have hh := (hint u).2; rw [he] at hh; norm_num at hh)
  choose U hU hpU hUb htrace using fun u : J =>
    source_subarc_internal_local_trace S a D.first D.first_embedded D.first_subset u.val
      (hint u).1 (hint u).2 b.imageᶜ (isCompact_range b.embedded.continuous).isClosed.isOpen_compl (hnotb u)
  let V : Set S := ⋃ u : J, U u
  have hV : IsOpen V := isOpen_iUnion hU
  have hcenter (u : Interval) (hu : u ∈ J) : F.N (u,⟨0,by norm_num⟩) ∈ V := by
    rw [F.first_center]
    exact Set.mem_iUnion.mpr ⟨⟨u,hu⟩,hpU ⟨u,hu⟩⟩
  obtain ⟨ρ,hρ,N,hN,hformula,hNc,hNV⟩ :=
    source_strip_finite_parameter_localization F.N F.first_embedding Unit (fun _=>J)
      (fun _=>isClosed_Icc) (fun _=>V) (fun _=>hV) (fun _=>hcenter)
  have hcenterN (u) : N (u,⟨0,by norm_num⟩)=D.first u := (hNc u).trans (F.first_center u)
  refine ⟨ρ,hρ,N,hN,hformula,hcenterN,?_⟩
  intro u hu w
  have hxV : N (u,w) ∈ V := hNV () (u,w) hu
  obtain ⟨v,hxU⟩ := Set.mem_iUnion.mp hxV
  refine ⟨hUb v hxU,?_⟩
  constructor
  · intro hxa
    obtain ⟨t,ht⟩ := (htrace v _ hxU).mp hxa
    have he : (u,w)=(t,⟨0,by norm_num⟩) := hN.injective (ht.symm.trans (hcenterN t).symm)
    exact congrArg (fun q : Interval × Set.Icc (-1:ℝ) 1 => (q.2:ℝ)) he
  · intro hw
    have he : w=(⟨0,by norm_num⟩ : Set.Icc (-1:ℝ) 1) := Subtype.ext hw
    rw [he,hcenterN]
    exact D.first_subset (Set.mem_range_self u)
end CurveComplex
#print axioms CurveComplex.source_first_framed_middle_uniform_avoidance
