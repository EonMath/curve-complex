import CurveComplexGenusTwo.Foundations.ActualIntersectionBridge
import Mathlib

namespace CurveComplex.LocalSurgery

/-- The arithmetic and finite-set step after mod-two invariance: a strict
excess cannot be supported by only one original transverse crossing. -/
theorem two_crossings_of_excess_and_parity
    {S : Type*} [TopologicalSpace S]
    (a b : EssentialCurve S) (ht : Transverse a.val b.val)
    (hexcess : geometricIntersection (Quotient.mk (essentialCurveSetoid S) a)
      (Quotient.mk (essentialCurveSetoid S) b) < ht.1.toFinset.card)
    (hparity : Nat.ModEq 2
      (geometricIntersection (Quotient.mk (essentialCurveSetoid S) a)
        (Quotient.mk (essentialCurveSetoid S) b)) ht.1.toFinset.card) :
    ∃ u v : S, u ∈ a.val.image ∩ b.val.image ∧
      v ∈ a.val.image ∩ b.val.image ∧ u ≠ v := by
  have htwo : 1 < ht.1.toFinset.card := by
    dsimp [Nat.ModEq] at hparity
    omega
  obtain ⟨u,v,hu,hv,huv⟩ := Finset.one_lt_card_iff.mp htwo
  exact ⟨u,v,by simpa using hu,by simpa using hv,huv⟩

#print axioms two_crossings_of_excess_and_parity

end CurveComplex.LocalSurgery
