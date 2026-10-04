import CurveComplexGenusTwo.Filtration.CarrierApproximation
import CurveComplexGenusTwo.Filtration.StarSmallHomologyEquiv
import CurveComplexGenusTwo.Filtration.ComparisonReduction

open CategoryTheory
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
namespace CurveGenusTwo.Filtration
universe u
variable {V : Type u} [LinearOrder V]

private theorem approximation_cast_range {ι : Type*} {F : ι → Type*}
    [∀ i, AddCommGroup (F i)] {i j : ι} (h : i = j)
    {A : Type*} [AddCommGroup A] (f : A →+ F i) :
    Eq.mp (congrArg (fun k => AddSubgroup (F k)) h) f.range =
      (Eq.mp (congrArg (fun k => A →+ F k) h) f).range := by
  cases h
  rfl

theorem approximation_boundaries_eq_positiveBoundary_range (K : FiniteComplex V) (n : ℕ) :
    boundaries K ((n + 1 : ℕ) : ℤ) = (positiveBoundary K (n + 1)).range := by
  have h : (((n + 1 : ℕ) : ℤ) + 1 - 1) = ((n + 1 : ℕ) : ℤ) := by omega
  have h' : (((n + 1 + 1 : ℕ) : ℤ) - 1) = ((n + 1 : ℕ) : ℤ) := by omega
  change Eq.mp (congrArg (fun k : ℤ => AddSubgroup (chains K k)) h)
      (boundary K (((n + 1 : ℕ) : ℤ) + 1)).range =
    (Eq.mp (congrArg (fun k : ℤ =>
      chains K ((n + 1 + 1 : ℕ) : ℤ) →+ chains K k) h')
      (boundary K ((n + 1 + 1 : ℕ) : ℤ))).range
  exact approximation_cast_range h (boundary K (((n + 1 : ℕ) : ℤ) + 1))

theorem starSmallSimplicialApproximation_maps_boundaries (K : FiniteComplex V) (n : ℕ)
    (c : FreeAbelianGroup (StarSmallSimplex K (n+1)))
    (hc : c ∈ (starSmallBoundary K (n+1)).range) :
    starSmallSimplicialApproximation K (n+1) c ∈ boundaries K ((n+1:ℕ):ℤ) := by
  obtain ⟨b, rfl⟩ := hc
  rw [approximation_boundaries_eq_positiveBoundary_range]
  exact ⟨starSmallSimplicialApproximation K (n+2) b,
    starSmallSimplicialApproximation_boundary K (n+1) b⟩

end CurveGenusTwo.Filtration
namespace CurveGenusTwo.Filtration
variable {V : Type} [LinearOrder V]

noncomputable def starSmallSimplicialHomologyMap (K : FiniteComplex V) (n : ℕ) :
    starSmallPositiveHomology K n →+ reducedHomology K ((n+1:ℕ):ℤ) :=
  QuotientAddGroup.map _ _ (starSmallSimplicialCyclesMap K n) (by
    intro c hc
    exact starSmallSimplicialApproximation_maps_boundaries K n c.1 hc)

/-- A reverse homology homomorphism built from actual subdivision and the
recursive simplicial carrier approximation. Its inverse laws are separate
comparison obligations. -/
noncomputable def carrierReversePositiveHomology (K : FiniteComplex V) (n : ℕ) :
    singularPositiveHomology K n →+ reducedHomology K ((n+1:ℕ):ℤ) :=
  (starSmallSimplicialHomologyMap K n).comp
    (starSmallPositiveHomologyEquiv K n).symm.toAddMonoidHom

/-- The remaining singular carrier-homotopy identity suffices for producer A.
The simplicial cycle is the approximation already constructed above. -/
theorem singularPositiveCycle_lift_of_approximation_homotopy
    (K : FiniteComplex V) (n : ℕ)
    (hhomotopy : ∀ a : (starSmallBoundary K n).ker,
      starSmallChainInclusion K (n+1) a.1 -
        (positiveCyclesMap K n (starSmallSimplicialCyclesMap K n a)).1 ∈
          singularPositiveBoundaries K n) :
    ∀ z : singularPositiveCycles K n,
      ∃ c : cycles K ((n+1:ℕ):ℤ),
        z.1 - (positiveCyclesMap K n c).1 ∈ singularPositiveBoundaries K n := by
  apply (singularPositiveCycle_lift_iff_starSmall K n).mpr
  intro a ha
  exact ⟨starSmallSimplicialCyclesMap K n ⟨a, ha⟩, hhomotopy ⟨a, ha⟩⟩

#print axioms starSmallSimplicialApproximation_maps_boundaries
#print axioms carrierReversePositiveHomology
#print axioms singularPositiveCycle_lift_of_approximation_homotopy
end CurveGenusTwo.Filtration
