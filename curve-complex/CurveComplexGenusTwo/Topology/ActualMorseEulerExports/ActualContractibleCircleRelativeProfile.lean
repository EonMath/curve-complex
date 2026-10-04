import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualPairIntegralEulerAdditivity
import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseStatements

namespace CurveComplexGenusTwo.CWHurewicz

open CategoryTheory CategoryTheory.Limits

/-- The actual disk/annulus pair profile, once the literal lower subspace has
been transported to a circle and the upper space has been proved contractible. -/
theorem actual_contractible_circle_pair_relative_profile
    (X : Type) [TopologicalSpace X] [ContractibleSpace X]
    (A : Set X) [PathConnectedSpace A]
    (e : ContinuousMap.HomotopyEquiv A Circle) :
    IsZero (relativeHomology X A 0) ∧
    IsZero (relativeHomology X A 1) ∧
    Nonempty (relativeHomology X A 2 ≅ ModuleCat.of ℤ ℤ) ∧
    ∀ n : ℕ, 3 ≤ n → IsZero (relativeHomology X A n) := by
  have hnat := CircleHomologyComputation.augmentation_naturality (pairInclusion X A)
  letI : IsIso (homologyInclusion X A 0) := IsIso.of_isIso_fac_right hnat
  have hzero0 : IsZero (relativeHomology X A 0) := by
    obtain ⟨hcomp, _⟩ := pairHomology_exact_at_absolute X A 0
    have hz : homologyToRelative X A 0 = 0 :=
      (cancel_epi (homologyInclusion X A 0)).mp (by simpa using hcomp)
    letI := actual_homologyToRelative_zero_epi X A
    exact IsZero.of_epi_eq_zero _ hz
  have hzero1 : IsZero (relativeHomology X A 1) := by
    obtain ⟨hc, _⟩ := pairHomology_exact_at_subspace X A 0
    have hd : relativeConnecting X A 0 = 0 :=
      (cancel_mono (homologyInclusion X A 0)).mp (by simpa using hc)
    obtain ⟨_, he⟩ := pairHomology_exact_at_relative X A 0
    exact he.isZero_X₂
      ((CircleHomologyComputation.contractible_positive_homology X 1 (by omega)).eq_of_src _ _)
      hd
  have hconn (k : ℕ) (hk : 0 < k) : IsIso (relativeConnecting X A k) := by
    have hz1 := CircleHomologyComputation.contractible_positive_homology X k hk
    have hz2 := CircleHomologyComputation.contractible_positive_homology X (k + 1) (by omega)
    obtain ⟨_, he1⟩ := pairHomology_exact_at_relative X A k
    obtain ⟨_, he0⟩ := pairHomology_exact_at_subspace X A k
    letI : Mono (relativeConnecting X A k) := he1.mono_g (hz2.eq_of_src _ _)
    letI : Epi (relativeConnecting X A k) := he0.epi_f (hz1.eq_of_tgt _ _)
    exact isIso_of_mono_of_epi _
  letI := hconn 1 (by omega)
  refine ⟨hzero0, hzero1, ⟨asIso (relativeConnecting X A 1) ≪≫
    CircleHomologyComputation.homotopyHomologyIso e 1 ≪≫
    CircleHomologyComputation.circleH1Iso⟩, ?_⟩
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  letI := hconn k (by omega)
  have haz : IsZero (H A k) :=
    (CircleHomologyComputation.circle_higher_homology k (by omega)).of_iso
      (CircleHomologyComputation.homotopyHomologyIso e k)
  exact haz.of_iso (asIso (relativeConnecting X A k))


end CurveComplexGenusTwo.CWHurewicz
