import CurveComplexGenusTwo.Topology.FirstReturnCorner.ActualRetainedBranchSquares
namespace CurveComplex
open Set Topology
/-- Produce the unique strictly internal closing-arc source parameter at
every actual retained crossing. The finite framing centers are real source
parameters; neither internality nor injectivity is assumed. -/
theorem source_retained_closing_framing_parameters
    {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : SourceFirstReturnBoundary a b)
    (B : SourceTwoSurgeryBranches D) (i : Bool) :
    ∃ θ : source_surgery_retained_crossings B i → Interval,
      Function.Injective θ ∧
      (∀ p, B.closing i (θ p)=p.val) ∧
      ∀ p, 0<(θ p:ℝ) ∧ (θ p:ℝ)<1 := by
  classical
  choose θ hθ using fun p : source_surgery_retained_crossings B i => p.property.1.1
  have hθ0 (p : source_surgery_retained_crossings B i) : θ p≠0 := by
    intro h
    apply p.property.2
    left
    exact (hθ p).symm.trans (h ▸ B.closing_zero i)
  have hθ1 (p : source_surgery_retained_crossings B i) : θ p≠1 := by
    intro h
    apply p.property.2
    right
    exact (hθ p).symm.trans (h ▸ B.closing_one i)
  refine ⟨θ,?_,hθ,?_⟩
  · intro p q he
    apply Subtype.ext
    exact (hθ p).symm.trans ((congrArg (B.closing i) he).trans (hθ q))
  · intro p
    refine ⟨lt_of_le_of_ne (θ p).property.1 ?_,lt_of_le_of_ne (θ p).property.2 ?_⟩
    · intro h
      apply hθ0 p
      exact Subtype.ext h.symm
    · intro h
      apply hθ1 p
      exact Subtype.ext h
end CurveComplex
#print axioms CurveComplex.source_retained_closing_framing_parameters
