import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualFirstReturnClosedPushedCurve
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualRetainedMiddleExactBudget
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualRetainedMiddleCrossing

namespace CurveComplex
open Set Topology Schoenflies

/-- Pending exact independent producer: the actual complete budget trace,
when realized by an actual embedded closed source Curve, is transverse to
both original curves. No final Transverse certificate is a hypothesis. -/
theorem source_first_return_budget_trace_transverse
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    {a b : Curve S} (D : SourceFirstReturnBoundary a b)
    (B : SourceTwoSurgeryBranches D) (ht : Transverse a b) (i : Bool)
    (P : SourceFirstReturnBudgetTracks D B i) (d : Curve S)
    (hd : d.image=P.trace) : Transverse a d ∧ Transverse b d := by
  have hfin := source_first_return_whole_trace_budget D B ht i P
  have hfa : (a.image ∩ d.image).Finite := by
    rw [Set.inter_comm,hd]
    exact hfin.1
  have hfb : (b.image ∩ d.image).Finite := by
    rw [Set.inter_comm,hd]
    exact hfin.2.1
  refine ⟨⟨hfa,?_⟩,⟨hfb,?_⟩⟩
  · rintro x ⟨hxa,hxd⟩
    rw [hd] at hxd
    rcases hxd with ((hxf | hxg) | hxc) | hxc
    · obtain ⟨u,hu,rfl⟩ := hxf
      exact (P.caps.width_nonzero.1 ((P.first_middle u hu P.caps.w).2.mp hxa)).elim
    · obtain ⟨u,hu,rfl⟩ := hxg
      obtain ⟨p,hup⟩ := (P.closing_middle u hu P.caps.z).2 hxa
      rw [hup]
      exact source_budget_retained_middle_crossing S P d hd p
    · exact (Set.disjoint_left.mp P.caps.start_avoids_target hxc hxa).elim
    · exact (source_budget_cap_crossing_transfer S P d hd true x hxc).1 hxa
  · rintro x ⟨hxb,hxd⟩
    rw [hd] at hxd
    rcases hxd with ((hxf | hxg) | hxc) | hxc
    · obtain ⟨u,hu,rfl⟩ := hxf
      exact ((P.first_middle u hu P.caps.w).1 hxb).elim
    · obtain ⟨u,hu,rfl⟩ := hxg
      exact (P.caps.width_nonzero.2 ((P.closing_middle u hu P.caps.z).1.mp hxb)).elim
    · exact (Set.disjoint_left.mp P.caps.start_avoids_current hxc hxb).elim
    · exact (source_budget_cap_crossing_transfer S P d hd true x hxc).2 hxb

end CurveComplex
#print axioms CurveComplex.source_first_return_budget_trace_transverse
