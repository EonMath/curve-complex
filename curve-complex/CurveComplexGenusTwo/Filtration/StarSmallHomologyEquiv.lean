import CurveComplexGenusTwo.Filtration.StarSmallHomology

open CategoryTheory
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
namespace CurveGenusTwo.Filtration
variable {V : Type} [LinearOrder V]

noncomputable abbrev starSmallPositiveCycles (K : FiniteComplex V) (n : ℕ) :=
  (starSmallBoundary K n).ker

noncomputable abbrev starSmallPositiveBoundaries (K : FiniteComplex V) (n : ℕ) :=
  (starSmallBoundary K (n+1)).range

noncomputable abbrev starSmallPositiveHomology (K : FiniteComplex V) (n : ℕ) :=
  (starSmallPositiveCycles K n) ⧸
    ((starSmallPositiveBoundaries K n).comap (starSmallPositiveCycles K n).subtype)

noncomputable def starSmallPositiveCyclesMap (K : FiniteComplex V) (n : ℕ) :
    starSmallPositiveCycles K n →+ singularPositiveCycles K n :=
  ((starSmallChainInclusion K (n+1)).comp (starSmallPositiveCycles K n).subtype).codRestrict
    (singularPositiveCycles K n) (by
      intro c
      change singularGeneratorBoundary K n (starSmallChainInclusion K (n+1) c.1) = 0
      rw [← starSmallChainInclusion_boundary, show starSmallBoundary K n c.1 = 0 from c.2,
        map_zero])

noncomputable def starSmallPositiveHomologyMap (K : FiniteComplex V) (n : ℕ) :
    starSmallPositiveHomology K n →+ singularPositiveHomology K n :=
  QuotientAddGroup.map _ _ (starSmallPositiveCyclesMap K n) (by
    rintro c ⟨b, hb⟩
    change (starSmallPositiveCyclesMap K n c).1 ∈ singularPositiveBoundaries K n
    refine ⟨starSmallChainInclusion K (n+2) b, ?_⟩
    rw [← starSmallChainInclusion_boundary, hb]
    rfl)

theorem starSmallPositiveHomologyMap_injective (K : FiniteComplex V) (n : ℕ) :
    Function.Injective (starSmallPositiveHomologyMap K n) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
    change QuotientAddGroup.mk (starSmallPositiveCyclesMap K n c) = 0 at hx
    have hb := (QuotientAddGroup.eq_zero_iff _).mp hx
    change starSmallChainInclusion K (n+1) c.1 ∈ singularPositiveBoundaries K n at hb
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    exact starSmallCycle_bounds_of_raw_bounds K n c.1 c.2 hb

theorem starSmallPositiveHomologyMap_surjective (K : FiniteComplex V) (n : ℕ) :
    Function.Surjective (starSmallPositiveHomologyMap K n) := by
  intro x
  induction x using QuotientAddGroup.induction_on with
  | _ z =>
    obtain ⟨c, hc, hz⟩ := singularPositiveCycle_has_smallComplex_representative K n z
    refine ⟨QuotientAddGroup.mk (⟨c, hc⟩ : starSmallPositiveCycles K n), ?_⟩
    change QuotientAddGroup.mk (starSmallPositiveCyclesMap K n ⟨c, hc⟩) =
      QuotientAddGroup.mk z
    apply QuotientAddGroup.eq.mpr
    change -(starSmallChainInclusion K (n+1) c) + z.1 ∈ singularPositiveBoundaries K n
    convert (singularPositiveBoundaries K n).neg_mem hz using 1 <;> abel

/-- Actual star-small singular chains compute positive singular homology. -/
noncomputable def starSmallPositiveHomologyEquiv (K : FiniteComplex V) (n : ℕ) :
    starSmallPositiveHomology K n ≃+ singularPositiveHomology K n :=
  AddEquiv.ofBijective (starSmallPositiveHomologyMap K n)
    ⟨starSmallPositiveHomologyMap_injective K n, starSmallPositiveHomologyMap_surjective K n⟩

#print axioms starSmallPositiveHomologyEquiv
end CurveGenusTwo.Filtration
