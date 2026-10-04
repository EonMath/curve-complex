import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualPairIntegralEulerAdditivity

namespace CurveComplexGenusTwo.CWHurewicz

open CategoryTheory CategoryTheory.Limits Function

/-- Finite generation of the actual relative group follows from the adjacent
actual absolute/subspace groups in the pair long exact sequence. -/
theorem actual_relativeHomology_positive_finite_of_absolute_and_subspace_finite
    (X : Type) [TopologicalSpace X] (A : Set X) (n : ℕ)
    [Module.Finite ℤ (H X (n + 1))] [Module.Finite ℤ (H A n)] :
    Module.Finite ℤ (relativeHomology X A (n + 1)) := by
  let f := (homologyToRelative X A (n + 1)).hom
  let g := (relativeConnecting X A n).hom
  letI : Module ℤ g.range := g.range.module
  letI : Module.Finite ℤ g.range := inferInstance
  obtain ⟨_, he⟩ := pairHomology_exact_at_relative X A n
  have hfg : Exact f g.rangeRestrict := by
    rw [LinearMap.exact_iff]
    simpa [f, g] using he.moduleCat_range_eq_ker.symm
  exact Module.Finite.of_exact hfg g.surjective_rangeRestrict


end CurveComplexGenusTwo.CWHurewicz
