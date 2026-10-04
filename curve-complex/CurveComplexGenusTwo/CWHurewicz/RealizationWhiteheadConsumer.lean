import CurveComplexGenusTwo.Foundations.RealizationCW
import CurveComplexGenusTwo.CWHurewicz.CWWhiteheadFromCellStep

namespace CurveComplexGenusTwo.CWHurewicz

/-- Whitehead applied to the actual finite-face weak geometric realization.
The all-positive-homotopy-groups premise is the remaining Hurewicz output. -/
theorem contractibleRealizationOfAllPiTrivial
    {V : Type} (K : AbstractSimplicialComplex V)
    [PathConnectedSpace (CurveComplex.RealizationPoint K)]
    (hpi : ∀ n : ℕ, 1 ≤ n → ∀ x : CurveComplex.RealizationPoint K,
      Subsingleton (HomotopyGroup.Pi n (CurveComplex.RealizationPoint K) x)) :
    ContractibleSpace (CurveComplex.RealizationPoint K) := by
  exact contractibleOfCWAllPiSubsingletonT2_actual hpi

end CurveComplexGenusTwo.CWHurewicz
