import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualPairIntegralEulerAdditivity
import CurveComplexGenusTwo.Topology.ActualDerivativeSignEuler.ActualIntegralHandleEulerAlgebra
import CurveComplexGenusTwo.CWHurewicz.PairExactnessInterface
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

namespace CurveComplexGenusTwo.CWHurewicz

open CategoryTheory CategoryTheory.Limits Function

theorem actual_H_finite_of_subspace_and_relative_finite
    (X : Type) [TopologicalSpace X] (A : Set X) (n : ℕ)
    [Module.Finite ℤ (H A n)] [Module.Finite ℤ (relativeHomology X A n)] :
    Module.Finite ℤ (H X n) := by
  let f := (homologyInclusion X A n).hom
  let g := (homologyToRelative X A n).hom
  letI : Module ℤ g.range := g.range.module
  obtain ⟨_, he⟩ := pairHomology_exact_at_absolute X A n
  have hgfinite : Module.Finite ℤ g.range := inferInstance
  have hfg : Exact f g.rangeRestrict := by
    rw [LinearMap.exact_iff]
    simpa [f, g] using he.moduleCat_range_eq_ker.symm
  exact Module.Finite.of_exact hfg g.surjective_rangeRestrict

set_option backward.isDefEq.respectTransparency false in
theorem actual_pair_integral_euler_additivity
    (X : Type) [TopologicalSpace X] (A : Set X)
    [hA0 : Module.Finite ℤ (H A 0)] [hA1 : Module.Finite ℤ (H A 1)]
    [hA2 : Module.Finite ℤ (H A 2)]
    [hX0 : Module.Finite ℤ (H X 0)] [hX1 : Module.Finite ℤ (H X 1)]
    [hX2 : Module.Finite ℤ (H X 2)]
    [hR0 : Module.Finite ℤ (relativeHomology X A 0)]
    [hR1 : Module.Finite ℤ (relativeHomology X A 1)]
    [hR2 : Module.Finite ℤ (relativeHomology X A 2)]
    (hthree : IsZero (relativeHomology X A 3)) :
    (Module.finrank ℤ (H X 0) : ℤ) - Module.finrank ℤ (H X 1) +
      Module.finrank ℤ (H X 2) =
    (Module.finrank ℤ (H A 0) : ℤ) - Module.finrank ℤ (H A 1) +
      Module.finrank ℤ (H A 2) +
      Module.finrank ℤ (relativeHomology X A 0) -
      Module.finrank ℤ (relativeHomology X A 1) +
      Module.finrank ℤ (relativeHomology X A 2) := by
  let V : Fin 10 → Type :=
    ![(H A 2 : Type), (H X 2 : Type), (relativeHomology X A 2 : Type),
      (H A 1 : Type), (H X 1 : Type), (relativeHomology X A 1 : Type),
      (H A 0 : Type), (H X 0 : Type), (relativeHomology X A 0 : Type),
      (Fin 0 → ℤ)]
  let (i : Fin 10) : AddCommGroup (V i) := match i with
    | 0 => (H A 2).isAddCommGroup | 1 => (H X 2).isAddCommGroup
    | 2 => (relativeHomology X A 2).isAddCommGroup
    | 3 => (H A 1).isAddCommGroup | 4 => (H X 1).isAddCommGroup
    | 5 => (relativeHomology X A 1).isAddCommGroup
    | 6 => (H A 0).isAddCommGroup | 7 => (H X 0).isAddCommGroup
    | 8 => (relativeHomology X A 0).isAddCommGroup
    | 9 => Pi.addCommGroup
  let (i : Fin 10) : Module ℤ (V i) := match i with
    | 0 => (H A 2).isModule | 1 => (H X 2).isModule
    | 2 => (relativeHomology X A 2).isModule
    | 3 => (H A 1).isModule | 4 => (H X 1).isModule
    | 5 => (relativeHomology X A 1).isModule
    | 6 => (H A 0).isModule | 7 => (H X 0).isModule
    | 8 => (relativeHomology X A 0).isModule
    | 9 => Pi.module _ _ _
  let (i : Fin 10) : Module.Finite ℤ (V i) := match i with
    | 0 => hA2 | 1 => hX2 | 2 => hR2
    | 3 => hA1 | 4 => hX1 | 5 => hR1
    | 6 => hA0 | 7 => hX0 | 8 => hR0
    | 9 => (show Module.Finite ℤ (Fin 0 → ℤ) from inferInstance)
  let f (i : Fin 9) : V i.castSucc →ₗ[ℤ] V i.succ := match i with
    | 0 => (homologyInclusion X A 2).hom
    | 1 => (homologyToRelative X A 2).hom
    | 2 => (relativeConnecting X A 1).hom
    | 3 => (homologyInclusion X A 1).hom
    | 4 => (homologyToRelative X A 1).hom
    | 5 => (relativeConnecting X A 0).hom
    | 6 => (homologyInclusion X A 0).hom
    | 7 => (homologyToRelative X A 0).hom
    | 8 => 0
  have hfirst : Injective (f 0) := by
    obtain ⟨_, he⟩ := pairHomology_exact_at_subspace X A 2
    have hm : Mono (homologyInclusion X A 2) :=
      he.mono_g (hthree.eq_of_src _ _)
    exact (ModuleCat.mono_iff_injective _).mp hm
  have hexact : ∀ i : Fin 8, Exact (f i.castSucc) (f i.succ) := by
    intro i
    fin_cases i
    · obtain ⟨_, he⟩ := pairHomology_exact_at_absolute X A 2
      exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp he
    · obtain ⟨_, he⟩ := pairHomology_exact_at_relative X A 1
      exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp he
    · obtain ⟨_, he⟩ := pairHomology_exact_at_subspace X A 1
      exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp he
    · obtain ⟨_, he⟩ := pairHomology_exact_at_absolute X A 1
      exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp he
    · obtain ⟨_, he⟩ := pairHomology_exact_at_relative X A 0
      exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp he
    · obtain ⟨_, he⟩ := pairHomology_exact_at_subspace X A 0
      exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp he
    · obtain ⟨_, he⟩ := pairHomology_exact_at_absolute X A 0
      exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp he
    · change Exact (homologyToRelative X A 0).hom
        (0 : relativeHomology X A 0 →ₗ[ℤ] (Fin 0 → ℤ))
      rw [LinearMap.exact_iff, LinearMap.ker_zero]
      exact (LinearMap.range_eq_top.mpr
        ((ModuleCat.epi_iff_surjective _).mp (actual_homologyToRelative_zero_epi X A))).symm
  have hlast : Surjective (f (Fin.last 8)) := by
    change Surjective (0 : relativeHomology X A 0 →ₗ[ℤ] (Fin 0 → ℤ))
    intro y
    exact ⟨0, Subsingleton.elim _ _⟩
  have h := actual_integral_euler_additivity_of_ten_term_exact_sequence
    (fun i => V i) f hfirst hexact hlast
  have hzero : Module.finrank ℤ (Fin 0 → ℤ) = 0 := Module.finrank_zero_of_subsingleton
  simpa [V, hzero] using h

theorem actual_H_zero_of_subspace_and_relative_zero
    (X : Type) [TopologicalSpace X] (A : Set X) (n : ℕ)
    (hA : IsZero (H A n)) (hR : IsZero (relativeHomology X A n)) :
    IsZero (H X n) := by
  obtain ⟨_, he⟩ := pairHomology_exact_at_absolute X A n
  exact he.isZero_X₂ (hA.eq_of_src _ _) (hR.eq_of_tgt _ _)

theorem actual_full_integral_singular_euler_eq_three_term
    (X : Type) [TopologicalSpace X]
    (hhigher : ∀ n : ℕ, 3 ≤ n → IsZero (H X n)) :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank ℤ (H X n) : ℤ)) =
      (Module.finrank ℤ (H X 0) : ℤ) - Module.finrank ℤ (H X 1) +
        Module.finrank ℤ (H X 2) := by
  classical
  have hr (n : ℕ) (hn : 3 ≤ n) : Module.finrank ℤ (H X n) = 0 := by
    letI := ModuleCat.subsingleton_of_isZero (hhigher n hn)
    exact Module.finrank_zero_of_subsingleton
  have hs : Function.support (fun n : ℕ =>
      (-1 : ℤ) ^ n * (Module.finrank ℤ (H X n) : ℤ)) ⊆ (Finset.range 3 : Set ℕ) := by
    intro n hn
    by_contra hnot
    have hlarge : 3 ≤ n := by simpa only [Finset.mem_coe, Finset.mem_range, not_lt] using hnot
    exact hn (by dsimp only; rw [hr n hlarge]; simp)
  rw [finsum_eq_sum_of_support_subset _ hs]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  ring

theorem actual_pair_integral_euler_increment_of_finite_relative_profile
    (X : Type) [TopologicalSpace X] (A : Set X)
    [Module.Finite ℤ (H A 0)] [Module.Finite ℤ (H A 1)]
    [Module.Finite ℤ (H A 2)]
    [Module.Finite ℤ (relativeHomology X A 0)]
    [Module.Finite ℤ (relativeHomology X A 1)]
    [Module.Finite ℤ (relativeHomology X A 2)]
    (hthree : IsZero (relativeHomology X A 3))
    {I : Type*} (S : Finset I) (k : I → Fin 3)
    (hr0 : Module.finrank ℤ (relativeHomology X A 0) =
      ∑ i ∈ S, if k i = 0 then 1 else 0)
    (hr1 : Module.finrank ℤ (relativeHomology X A 1) =
      ∑ i ∈ S, if k i = 1 then 1 else 0)
    (hr2 : Module.finrank ℤ (relativeHomology X A 2) =
      ∑ i ∈ S, if k i = 2 then 1 else 0) :
    (Module.finrank ℤ (H X 0) : ℤ) - Module.finrank ℤ (H X 1) +
      Module.finrank ℤ (H X 2) =
    (Module.finrank ℤ (H A 0) : ℤ) - Module.finrank ℤ (H A 1) +
      Module.finrank ℤ (H A 2) + ∑ i ∈ S, (-1 : ℤ) ^ (k i : ℕ) := by
  letI := actual_H_finite_of_subspace_and_relative_finite X A 0
  letI := actual_H_finite_of_subspace_and_relative_finite X A 1
  letI := actual_H_finite_of_subspace_and_relative_finite X A 2
  have h := actual_pair_integral_euler_additivity X A hthree
  rw [hr0, hr1, hr2] at h
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at h
  rw [actual_finite_morse_index_sign_sum S k]
  linarith

end CurveComplexGenusTwo.CWHurewicz
