import CurveComplexGenusTwo.Dictionary.Circle24.ActualPrescribedOuterEdges
open Set Topology
namespace CurveComplex.BranchedDoubleCover
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]

/-- An actual lifted exterior arc and its deck mate exhaust precisely the
full preimage of that exterior arc; this applies to the retained second half
of each once-around rectangular boundary lift. -/
theorem late_boundary_fiber_range (q : BranchedDoubleCover E S)
    (β : C(Interval,S)) (γ : C(Interval,E))
    (hπ : ∀ t, q.projection (γ t)=β t) :
    Set.range (fun t : Interval => γ (CurveComplex.lateInterval t)) ∪
      Set.range (fun t : Interval => q.deck (γ (CurveComplex.lateInterval t)))=
      q.projection ⁻¹' Set.range (fun t : Interval => β (CurveComplex.lateInterval t)) := by
  ext e
  constructor
  · rintro (⟨t,rfl⟩ | ⟨t,rfl⟩)
    · exact ⟨t,(hπ _).symm⟩
    · exact ⟨t,(q.projection_deck _).trans (hπ _) |>.symm⟩
  · rintro ⟨t,ht⟩
    have he : q.projection (γ (CurveComplex.lateInterval t))=q.projection e := (hπ _).trans ht
    rcases (q.fiber_pair _ _).mp he with he | he
    · exact Or.inl ⟨t,he.symm⟩
    · exact Or.inr ⟨t,he.symm⟩

end CurveComplex.BranchedDoubleCover
#print axioms CurveComplex.BranchedDoubleCover.late_boundary_fiber_range
