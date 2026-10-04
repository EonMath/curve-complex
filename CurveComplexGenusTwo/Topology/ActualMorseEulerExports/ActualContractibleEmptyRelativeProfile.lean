import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualSublevelEulerEndpoints
import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseStatements

namespace CurveComplexGenusTwo.CWHurewicz

open CategoryTheory CategoryTheory.Limits

/-- The actual minimum-handle pair has an empty lower subspace. -/
theorem actual_homologyToRelative_isIso_of_empty_subspace
    (X : Type) [TopologicalSpace X] (A : Set X) [IsEmpty A] (n : ℕ) :
    IsIso (homologyToRelative X A n) := by
  cases n with
  | zero =>
      obtain ⟨_, he⟩ := pairHomology_exact_at_absolute X A 0
      letI : Mono (homologyToRelative X A 0) :=
        he.mono_g ((actual_integral_singular_homology_zero_of_isEmpty A 0).eq_of_src _ _)
      letI := actual_homologyToRelative_zero_epi X A
      exact isIso_of_mono_of_epi _
  | succ n =>
      exact homologyToRelative_isIso_of_subspace_zero X A n
        (actual_integral_singular_homology_zero_of_isEmpty A (n + 1))
        (actual_integral_singular_homology_zero_of_isEmpty A n)

theorem actual_contractible_empty_pair_relative_profile
    (X : Type) [TopologicalSpace X] [ContractibleSpace X]
    (A : Set X) [IsEmpty A] :
    Nonempty (relativeHomology X A 0 ≅ ModuleCat.of ℤ ℤ) ∧
      ∀ n : ℕ, 0 < n → IsZero (relativeHomology X A n) := by
  have hi (n : ℕ) := actual_homologyToRelative_isIso_of_empty_subspace X A n
  letI := hi 0
  refine ⟨⟨(asIso (homologyToRelative X A 0)).symm ≪≫
    asIso ((TopCat.of X).singularHomology₀ε (ModuleCat.of ℤ ℤ))⟩, ?_⟩
  intro n hn
  letI := hi n
  exact (CircleHomologyComputation.contractible_positive_homology X n hn).of_iso
    (asIso (homologyToRelative X A n)).symm


end CurveComplexGenusTwo.CWHurewicz
