import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualFirstReturnClosedPushedCurve
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualRetainedMiddleExactBudget
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualSubarcLocalTrace

namespace CurveComplex
open Set Topology Schoenflies

theorem source_crossing_transfer_shared_internal_subarc
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    (a c d : Curve S) (f : C(Interval,S)) (hf : IsEmbedding f)
    (hc : Set.range f ⊆ c.image) (hd : Set.range f ⊆ d.image)
    (t : Interval) (ht0 : 0 < (t:ℝ)) (ht1 : (t:ℝ) < 1)
    (hcross : CrossesAt a c (f t)) : CrossesAt a d (f t) := by
  obtain ⟨U,hU,hpU,_,htraceU⟩ := source_subarc_internal_local_trace S c f hf hc t ht0 ht1
    Set.univ isOpen_univ (Set.mem_univ _)
  obtain ⟨V,hV,hpV,_,htraceV⟩ := source_subarc_internal_local_trace S d f hf hd t ht0 ht1
    Set.univ isOpen_univ (Set.mem_univ _)
  exact source_crossing_transfer_local_trace hcross (U ∩ V) (hU.inter hV) ⟨hpU,hpV⟩
    (fun x hx => (htraceV x hx.2).trans (htraceU x hx.1).symm)

theorem source_budget_cap_ports_avoid_originals
    {S : Type} [TopologicalSpace S] {a b : Curve S}
    {D : SourceFirstReturnBoundary a b} {B : SourceTwoSurgeryBranches D} {i : Bool}
    (P : SourceFirstReturnBudgetTracks D B i) (k : Bool) :
    P.caps.C k 0 ∉ a.image ∧ P.caps.C k 0 ∉ b.image ∧
    P.caps.C k 1 ∉ a.image ∧ P.caps.C k 1 ∉ b.image := by
  have hf : P.F.θf k ∈ Set.Icc (P.F.θf false) (P.F.θf true) := by
    cases k
    · exact ⟨le_rfl,P.F.first_ports_order.le⟩
    · exact ⟨P.F.first_ports_order.le,le_rfl⟩
  have hg : P.F.θg k ∈ Set.Icc (P.F.θg false) (P.F.θg true) := by
    cases k
    · exact ⟨le_rfl,P.F.closing_ports_order.le⟩
    · exact ⟨P.F.closing_ports_order.le,le_rfl⟩
  rw [P.caps.first_port,P.caps.closing_port]
  have hframe := P.F.closing_framing k (P.F.θg k) P.caps.z
    (by simpa using (P.F.corner_positive k).2.2.2)
  refine ⟨fun ha => P.caps.width_nonzero.1 ((P.first_middle _ hf _).2.mp ha),
    (P.first_middle _ hf _).1,?_,
    fun hb => P.caps.width_nonzero.2 ((P.closing_middle _ hg _).1.mp hb)⟩
  intro ha
  have hz := (P.F.target_axis k _ hframe.1).mp ha
  have hcoord := congrArg (fun q : Plane => q 0) hframe.2
  change P.F.E k (P.F.M (P.F.θg k,P.caps.z)) 0 =
    P.F.E k (B.closing i (P.F.θg k)) 0 at hcoord
  exact (P.F.closing_height k).1.ne' (hcoord.symm.trans hz)

theorem source_budget_cap_crossing_transfer
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    {a b : Curve S} {D : SourceFirstReturnBoundary a b}
    {B : SourceTwoSurgeryBranches D} {i : Bool}
    (P : SourceFirstReturnBudgetTracks D B i) (d : Curve S) (hd : d.image=P.trace)
    (k : Bool) (p : S) (hp : p ∈ Set.range (P.caps.C k)) :
    (p ∈ a.image → CrossesAt a d p) ∧ (p ∈ b.image → CrossesAt b d p) := by
  have hsub : Set.range (P.caps.C k) ⊆ d.image := by
    rw [hd]
    intro x hx
    cases k
    · exact Or.inl (Or.inr hx)
    · exact Or.inr hx
  obtain ⟨t,rfl⟩ := hp
  have hports := source_budget_cap_ports_avoid_originals P k
  constructor
  · intro ha
    have ht0 : 0 < (t:ℝ) := by
      apply lt_of_le_of_ne t.property.1
      intro he
      have ht : t=0 := Subtype.ext he.symm
      exact hports.1 (ht ▸ ha)
    have ht1 : (t:ℝ) < 1 := by
      apply lt_of_le_of_ne t.property.2
      intro he
      have ht : t=1 := Subtype.ext he
      exact hports.2.2.1 (ht ▸ ha)
    exact source_crossing_transfer_shared_internal_subarc S a P.caps.d d (P.caps.C k)
      (P.caps.embedding k) (fun x hx => (P.caps.subset k hx).2) hsub t ht0 ht1
      (P.caps.target_crosses k _ ⟨Set.mem_range_self _,ha⟩)
  · intro hb
    have ht0 : 0 < (t:ℝ) := by
      apply lt_of_le_of_ne t.property.1
      intro he
      have ht : t=0 := Subtype.ext he.symm
      exact hports.2.1 (ht ▸ hb)
    have ht1 : (t:ℝ) < 1 := by
      apply lt_of_le_of_ne t.property.2
      intro he
      have ht : t=1 := Subtype.ext he
      exact hports.2.2.2 (ht ▸ hb)
    exact source_crossing_transfer_shared_internal_subarc S b P.caps.d d (P.caps.C k)
      (P.caps.embedding k) (fun x hx => (P.caps.subset k hx).2) hsub t ht0 ht1
      (P.caps.current_crosses k _ ⟨Set.mem_range_self _,hb⟩)
end CurveComplex
#print axioms CurveComplex.source_budget_cap_crossing_transfer
