import CurveComplexGenusTwo.Topology.ActualDerivativeSignEuler.ActualSublevelIntegralEuler

open CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz

theorem actual_sublevel_filtration_integral_finiteness_and_vanishing
    {E : Type} [TopologicalSpace E] (F : E → ℝ)
    (N : ℕ) (a : ℕ → ℝ)
    (ha : ∀ i < N, a i ≤ a (i + 1))
    (hbase : ∀ n : ℕ, IsZero (H {x : E // F x ≤ a 0} n))
    (hfinite : ∀ i < N, ∀ n : ℕ, n ≤ 2 →
      Module.Finite ℤ (relativeHomology {x : E // F x ≤ a (i + 1)}
        {x | F x.1 ≤ a i} n))
    (hzero : ∀ i < N, ∀ n : ℕ, 3 ≤ n →
      IsZero (relativeHomology {x : E // F x ≤ a (i + 1)}
        {x | F x.1 ≤ a i} n)) :
    (∀ i ≤ N, ∀ n : ℕ, n ≤ 2 → Module.Finite ℤ (H {x : E // F x ≤ a i} n)) ∧
    (∀ i ≤ N, ∀ n : ℕ, 3 ≤ n → IsZero (H {x : E // F x ≤ a i} n)) := by
  constructor
  · intro i
    induction i with
    | zero =>
        intro _ n _
        letI := ModuleCat.subsingleton_of_isZero (hbase n)
        exact Module.Finite.of_injective
          (0 : H {x : E // F x ≤ a 0} n →ₗ[ℤ] ℤ)
          (fun _ _ _ => Subsingleton.elim _ _)
    | succ i ih =>
        intro hi n hn
        have hiN : i < N := by omega
        letI := ih (by omega) n hn
        letI := hfinite i hiN n hn
        exact actual_sublevel_integral_H_finite_of_relative_finite F (a i) (a (i + 1))
          (ha i hiN) n
  · intro i
    induction i with
    | zero => intro _ n _; exact hbase n
    | succ i ih =>
        intro hi n hn
        have hiN : i < N := by omega
        exact actual_sublevel_integral_H_zero_of_relative_zero F (a i) (a (i + 1))
          (ha i hiN) n (ih (by omega) n hn) (hzero i hiN n hn)

theorem actual_sublevel_full_integral_euler_telescope_of_finite_relative_profiles
    {E : Type} [TopologicalSpace E] (F : E → ℝ)
    (N : ℕ) (a : ℕ → ℝ) {I : Type*} (S : ℕ → Finset I) (k : I → Fin 3)
    (ha : ∀ i < N, a i ≤ a (i + 1))
    (hbase : ∀ n : ℕ, IsZero (H {x : E // F x ≤ a 0} n))
    (hfinite : ∀ i < N, ∀ n : ℕ, n ≤ 2 →
      Module.Finite ℤ (relativeHomology {x : E // F x ≤ a (i + 1)}
        {x | F x.1 ≤ a i} n))
    (hzero : ∀ i < N, ∀ n : ℕ, 3 ≤ n →
      IsZero (relativeHomology {x : E // F x ≤ a (i + 1)}
        {x | F x.1 ≤ a i} n))
    (hprofile : ∀ i < N, ∀ j : Fin 3,
      Module.finrank ℤ (relativeHomology {x : E // F x ≤ a (i + 1)}
        {x | F x.1 ≤ a i} (j : ℕ)) = ∑ q ∈ S i, if k q = j then 1 else 0) :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      (Module.finrank ℤ (H {x : E // F x ≤ a N} n) : ℤ)) =
      ∑ i ∈ Finset.range N, ∑ q ∈ S i, (-1 : ℤ) ^ (k q : ℕ) := by
  obtain ⟨hF, hZ⟩ := actual_sublevel_filtration_integral_finiteness_and_vanishing
    F N a ha hbase hfinite hzero
  let χ (i : ℕ) : ℤ :=
    (Module.finrank ℤ (H {x : E // F x ≤ a i} 0) : ℤ) -
      Module.finrank ℤ (H {x : E // F x ≤ a i} 1) +
      Module.finrank ℤ (H {x : E // F x ≤ a i} 2)
  let c (i : ℕ) : ℤ := ∑ q ∈ S i, (-1 : ℤ) ^ (k q : ℕ)
  have hstep : ∀ i < N, χ (i + 1) = χ i + c i := by
    intro i hi
    letI := hF i (by omega) 0 (by omega)
    letI := hF i (by omega) 1 (by omega)
    letI := hF i (by omega) 2 (by omega)
    letI := hfinite i hi 0 (by omega)
    letI := hfinite i hi 1 (by omega)
    letI := hfinite i hi 2 (by omega)
    exact actual_sublevel_integral_euler_increment_of_finite_relative_profile
      F (a i) (a (i + 1)) (ha i hi) (hzero i hi 3 (by omega)) (S i) k
      (hprofile i hi 0) (hprofile i hi 1) (hprofile i hi 2)
  have hχ0 : χ 0 = 0 := by
    have hz (n : ℕ) : Module.finrank ℤ (H {x : E // F x ≤ a 0} n) = 0 := by
      letI := ModuleCat.subsingleton_of_isZero (hbase n)
      exact Module.finrank_zero_of_subsingleton
    simp [χ, hz]
  rw [actual_full_integral_singular_euler_eq_three_term
    {x : E // F x ≤ a N} (hZ N le_rfl)]
  change χ N = _
  rw [actual_integral_finite_event_euler_telescoping N χ c hstep, hχ0, zero_add]
