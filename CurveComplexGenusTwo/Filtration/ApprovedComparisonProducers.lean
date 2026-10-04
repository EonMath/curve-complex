import CurveComplexGenusTwo.Filtration.UniverseComparison
open CategoryTheory Topology Convexity
open scoped Simplicial
namespace CurveGenusTwo.Filtration
universe u
variable {V : Type u} [LinearOrder V]
-- Producer A: actual cycle lifting modulo actual singular boundaries.
theorem singularPositiveCycle_lift_mod_boundaries :
  ∀ (K : FiniteComplex V) (n : ℕ) (z : singularPositiveCycles K n),
  ∃ c : cycles K ((n + 1 : ℕ) : ℤ),
    z.1 - (positiveCyclesMap K n c).1 ∈ singularPositiveBoundaries K n := by
  intro K n
  apply (UniverseSubdivision.singularPositiveCycle_lift_iff_starSmall K n).mpr
  intro a ha
  exact ⟨normalizedStarSmallCyclesMap K n ⟨a, ha⟩,
    normalizedStarSmallCyclesMap_realization K n ⟨a, ha⟩⟩
-- Producer B: actual boundary reflection, no injectivity/iso hypothesis.
theorem positiveCyclesMap_reflects_boundaries :
  ∀ (K : FiniteComplex V) (n : ℕ)
    (c : cycles K ((n + 1 : ℕ) : ℤ)),
  (positiveCyclesMap K n c).1 ∈ singularPositiveBoundaries K n →
    c.1 ∈ boundaries K ((n + 1 : ℕ) : ℤ) := by
  exact UniverseSubdivision.positiveCyclesMap_reflects_boundaries
#print axioms singularPositiveCycle_lift_mod_boundaries
#print axioms positiveCyclesMap_reflects_boundaries
set_option pp.universes true in
#check @singularPositiveCycle_lift_mod_boundaries
set_option pp.universes true in
#check @positiveCyclesMap_reflects_boundaries
end CurveGenusTwo.Filtration
