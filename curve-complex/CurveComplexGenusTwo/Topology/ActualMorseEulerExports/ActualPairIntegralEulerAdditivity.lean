import Mathlib.Algebra.Exact.Sequence
import Mathlib.LinearAlgebra.Dimension.Localization
import CurveComplexGenusTwo.CWHurewicz.PairExactnessInterface
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

namespace CurveComplexGenusTwo.CWHurewicz

open CategoryTheory CategoryTheory.Limits Function

set_option backward.isDefEq.respectTransparency false in
/-- The actual pair projection is onto in degree zero. -/
theorem actual_homologyToRelative_zero_epi
    (X : Type) [TopologicalSpace X] (A : Set X) :
    Epi (homologyToRelative X A 0) := by
  let S := pairHomologyShortComplex X A
  have hS := pairHomologyShortExact X A
  letI : Epi S.g := hS.epi_g
  change Epi (HomologicalComplex.homologyMap S.g 0)
  exact HomologicalComplex.epi_homologyMap_of_epi_of_not_rel S.g 0
    (by intro j; simp)

end CurveComplexGenusTwo.CWHurewicz
