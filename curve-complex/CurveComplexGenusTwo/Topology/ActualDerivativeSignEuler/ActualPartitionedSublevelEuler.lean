import CurveComplexGenusTwo.Topology.ActualDerivativeSignEuler.ActualSublevelEulerEndpoints

open CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz

theorem actual_finite_morse_event_sum_eq_critical_sum
    {I : Type*} [DecidableEq I] (N : ℕ) (S : ℕ → Finset I)
    (Z : Finset I) (k : I → Fin 3)
    (hdisjoint : Set.PairwiseDisjoint (↑(Finset.range N)) S)
    (hcover : (Finset.range N).biUnion S = Z) :
    (∑ i ∈ Finset.range N, ∑ q ∈ S i, (-1 : ℤ) ^ (k q : ℕ)) =
      ∑ q ∈ Z, (-1 : ℤ) ^ (k q : ℕ) := by
  rw [← Finset.sum_biUnion hdisjoint, hcover]

theorem actual_full_integral_euler_of_partitioned_sublevel_relative_profiles
    {E : Type} [TopologicalSpace E] [DecidableEq E] (F : E → ℝ)
    (N : ℕ) (a : ℕ → ℝ) (S : ℕ → Finset E) (Z : Finset E) (k : E → Fin 3)
    (ha : ∀ i < N, a i ≤ a (i + 1))
    (hbottom : ∀ x : E, a 0 < F x) (htop : ∀ x : E, F x ≤ a N)
    (hfinite : ∀ i < N, ∀ n : ℕ, n ≤ 2 →
      Module.Finite ℤ (relativeHomology {x : E // F x ≤ a (i + 1)}
        {x | F x.1 ≤ a i} n))
    (hzero : ∀ i < N, ∀ n : ℕ, 3 ≤ n →
      IsZero (relativeHomology {x : E // F x ≤ a (i + 1)}
        {x | F x.1 ≤ a i} n))
    (hprofile : ∀ i < N, ∀ j : Fin 3,
      Module.finrank ℤ (relativeHomology {x : E // F x ≤ a (i + 1)}
        {x | F x.1 ≤ a i} (j : ℕ)) = ∑ q ∈ S i, if k q = j then 1 else 0)
    (hdisjoint : Set.PairwiseDisjoint (↑(Finset.range N)) S)
    (hcover : (Finset.range N).biUnion S = Z) :
    (∑ q ∈ Z, (-1 : ℤ) ^ (k q : ℕ)) =
      (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
        (Module.finrank ℤ (CurveComplex.integralHomology E n) : ℤ)) := by
  have h := actual_full_integral_euler_of_sublevel_relative_profiles
    F N a S k ha hbottom htop hfinite hzero hprofile
  rw [actual_finite_morse_event_sum_eq_critical_sum N S Z k hdisjoint hcover] at h
  exact h.symm

theorem actual_continuous_compact_scalar_has_strict_endpoint_bounds
    {E : Type*} [TopologicalSpace E] [CompactSpace E]
    (F : E → ℝ) (hF : Continuous F) :
    ∃ a b : ℝ, a < b ∧ (∀ x : E, a < F x) ∧ (∀ x : E, F x < b) := by
  have hc : IsCompact (Set.range F) := isCompact_range hF
  obtain ⟨u, hu⟩ := hc.bddAbove
  obtain ⟨l, hl⟩ := hc.bddBelow
  let a := min l u - 1
  let b := max l u + 1
  refine ⟨a, b, ?_, ?_, ?_⟩
  · dsimp [a, b]
    have hmu : min l u ≤ max l u := min_le_max
    linarith
  · intro x
    have hx := hl (Set.mem_range_self x)
    have := min_le_left l u
    dsimp [a]
    linarith
  · intro x
    have hx := hu (Set.mem_range_self x)
    have := le_max_right l u
    dsimp [b]
    linarith
