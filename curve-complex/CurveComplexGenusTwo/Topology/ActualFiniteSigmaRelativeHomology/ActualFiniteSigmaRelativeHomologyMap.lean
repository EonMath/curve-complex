import CurveComplexGenusTwo.CWHurewicz.PairNaturality
import Mathlib.Topology.ContinuousMap.Sigma
import Mathlib.LinearAlgebra.Pi
import CurveComplexGenusTwo.Topology.ActualFiniteDiscDetection.FiniteWithSingletonCandidate
import CurveComplexGenusTwo.Topology.ActualFiniteSigmaRelativeHomology.FiniteSigmaRelativeChains

open CategoryTheory
open CurveComplexGenusTwo.CWHurewicz
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- The canonical finite assembly map for the supplied actual relative pairs.
Its i-th summand is the homology map of the literal inclusion x ↦ ⟨i,x⟩
applied to the i-th supplied homology class. -/
noncomputable def actual_finite_sigma_pair_relative_inclusion_sum
    (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, TopologicalSpace (K i)]
    (A : ∀ i, Set (K i)) (n : ℕ) :
    (∀ i, relativeHomology (K i) (A i) n) →ₗ[ℤ]
      relativeHomology (Σ i, K i) {z : Σ i, K i | z.2 ∈ A z.1} n where
  toFun h := ∑ i : ι,
    pairRelativeHomologyMap (A i) {z : Σ j, K j | z.2 ∈ A z.1}
      (ContinuousMap.sigmaMk (X := K) i) (fun _ hx => hx) n (h i)
  map_add' := by
    intro h g
    simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' := by
    intro r h
    simp only [Pi.smul_apply, RingHom.id_apply,
      ← Int.cast_smul_eq_zsmul ℤ, Int.cast_id, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact (pairRelativeHomologyMap (A i) {z : Σ j, K j | z.2 ∈ A z.1}
      (ContinuousMap.sigmaMk (X := K) i) (fun _ hx => hx) n).hom.map_smul r (h i)

/-- The complete defining action, in every natural degree including zero. -/
theorem actual_finite_sigma_pair_relative_inclusion_sum_apply
    (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, TopologicalSpace (K i)]
    (A : ∀ i, Set (K i)) (n : ℕ)
    (h : ∀ i, relativeHomology (K i) (A i) n) :
    actual_finite_sigma_pair_relative_inclusion_sum ι K A n h =
      ∑ i : ι, pairRelativeHomologyMap (A i) {z : Σ j, K j | z.2 ∈ A z.1}
        (ContinuousMap.sigmaMk (X := K) i) (fun _ hx => hx) n (h i) := by rfl

/-- The specified inclusion-sum map is invertible in every natural degree.
No nonempty index or component, and no positive-degree restriction, is assumed. -/
theorem actual_finite_sigma_pair_relative_inclusion_sum_bijective
    (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, TopologicalSpace (K i)]
    (A : ∀ i, Set (K i)) (n : ℕ) :
    Function.Bijective (actual_finite_sigma_pair_relative_inclusion_sum ι K A n) := by
  constructor
  · intro h g heq
    funext i
    have hi := congrArg (FiniteSigmaRelativeChains.componentHomology ι K A n i) heq
    change FiniteSigmaRelativeChains.componentHomology ι K A n i
      (∑ j : ι, FiniteSigmaRelativeChains.inclusionHomology ι K A n j (h j)) =
      FiniteSigmaRelativeChains.componentHomology ι K A n i
        (∑ j : ι, FiniteSigmaRelativeChains.inclusionHomology ι K A n j (g j)) at hi
    simpa only [FiniteSigmaRelativeChains.inclusion_component_sum_homology_apply] using hi
  · intro r
    refine ⟨fun i => FiniteSigmaRelativeChains.componentHomology ι K A n i r, ?_⟩
    exact FiniteSigmaRelativeChains.component_inclusion_sum_homology_apply ι K A n r
