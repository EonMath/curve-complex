import CurveComplexGenusTwo.Topology.ActualDerivativeSignEuler.ActualPartitionedSublevelEuler

open Set CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz

noncomputable section

private theorem windowed_integral_euler_telescope
    {E : Type} [TopologicalSpace E] [DecidableEq E]
    (F : E → ℝ) (N : ℕ) (a l u : ℕ → ℝ)
    (S : ℕ → Finset E) (Z : Finset E) (k : E → Fin 3)
    (hbottom : ∀ x, a 0 < F x) (htop : ∀ x, F x ≤ a N)
    (horder : ∀ i < N, a i ≤ l i ∧ l i ≤ u i ∧ u i ≤ a (i + 1))
    (hbefore : ∀ i < N, ∀ n : ℕ,
      IsZero (relativeHomology {x : E // F x ≤ l i} {x | F x.1 ≤ a i} n))
    (hafter : ∀ i < N, ∀ n : ℕ,
      IsZero (relativeHomology {x : E // F x ≤ a (i + 1)} {x | F x.1 ≤ u i} n))
    (hfinite : ∀ i < N, ∀ n : ℕ,
      Module.Finite ℤ (relativeHomology {x : E // F x ≤ u i} {x | F x.1 ≤ l i} n))
    (hzero : ∀ i < N, ∀ n : ℕ, 3 ≤ n →
      IsZero (relativeHomology {x : E // F x ≤ u i} {x | F x.1 ≤ l i} n))
    (hprofile : ∀ i < N, ∀ j : Fin 3,
      Module.finrank ℤ (relativeHomology {x : E // F x ≤ u i}
        {x | F x.1 ≤ l i} j.val) = ∑ q ∈ S i, if k q = j then 1 else 0)
    (hdisjoint : Set.PairwiseDisjoint (↑(Finset.range N)) S)
    (hcover : (Finset.range N).biUnion S = Z) :
    (∑ q ∈ Z, (-1 : ℤ) ^ (k q : ℕ)) =
      ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
        (Module.finrank ℤ (CurveComplex.integralHomology E n) : ℤ) := by
  let b : ℕ → ℝ := fun m => if m % 3 = 0 then a (m / 3) else
    if m % 3 = 1 then l (m / 3) else u (m / 3)
  let T : ℕ → Finset E := fun m => if m % 3 = 1 then S (m / 3) else ∅
  have hb0 (i : ℕ) : b (3 * i) = a i := by simp [b]
  have hb1 (i : ℕ) : b (3 * i + 1) = l i := by
    simp [b, Nat.add_div, Nat.add_mod]
  have hb2 (i : ℕ) : b (3 * i + 2) = u i := by
    simp [b, Nat.add_div, Nat.add_mod]
  have ht0 (i : ℕ) : T (3 * i) = ∅ := by simp [T]
  have ht1 (i : ℕ) : T (3 * i + 1) = S i := by
    simp [T, Nat.add_div, Nat.add_mod]
  have ht2 (i : ℕ) : T (3 * i + 2) = ∅ := by simp [T, Nat.add_mod]
  have hstages (m : ℕ) (hm : m < 3 * N) :
      m / 3 < N ∧ (m = 3 * (m / 3) ∨
        m = 3 * (m / 3) + 1 ∨ m = 3 * (m / 3) + 2) := by omega
  have hbmono : ∀ m < 3 * N, b m ≤ b (m + 1) := by
    intro m hm
    obtain ⟨hi, hm0 | hm1 | hm2⟩ := hstages m hm
    · rw [hm0, hb0, hb1]
      exact (horder _ hi).1
    · rw [hm1, show 3 * (m / 3) + 1 + 1 = 3 * (m / 3) + 2 by omega, hb1, hb2]
      exact (horder _ hi).2.1
    · rw [hm2, show 3 * (m / 3) + 2 + 1 = 3 * (m / 3 + 1) by omega, hb2, hb0]
      exact (horder _ hi).2.2
  have hzfinite {M : ModuleCat ℤ} (hM : IsZero M) : Module.Finite ℤ M := by
    letI := ModuleCat.subsingleton_of_isZero hM
    exact Module.Finite.of_injective (0 : M →ₗ[ℤ] ℤ)
      (fun _ _ _ => Subsingleton.elim _ _)
  have hzrank {M : ModuleCat ℤ} (hM : IsZero M) : Module.finrank ℤ M = 0 := by
    letI := ModuleCat.subsingleton_of_isZero hM
    exact Module.finrank_zero_of_subsingleton
  have hbfinite : ∀ m < 3 * N, ∀ n : ℕ, n ≤ 2 →
      Module.Finite ℤ (relativeHomology {x : E // F x ≤ b (m + 1)}
        {x | F x.1 ≤ b m} n) := by
    intro m hm n _
    obtain ⟨hi, hm0 | hm1 | hm2⟩ := hstages m hm
    · rw [hm0, hb0, hb1]
      exact hzfinite (hbefore _ hi n)
    · rw [hm1, show 3 * (m / 3) + 1 + 1 = 3 * (m / 3) + 2 by omega, hb1, hb2]
      exact hfinite _ hi n
    · rw [hm2, show 3 * (m / 3) + 2 + 1 = 3 * (m / 3 + 1) by omega, hb2, hb0]
      exact hzfinite (hafter _ hi n)
  have hbzero : ∀ m < 3 * N, ∀ n : ℕ, 3 ≤ n →
      IsZero (relativeHomology {x : E // F x ≤ b (m + 1)} {x | F x.1 ≤ b m} n) := by
    intro m hm n hn
    obtain ⟨hi, hm0 | hm1 | hm2⟩ := hstages m hm
    · rw [hm0, hb0, hb1]
      exact hbefore _ hi n
    · rw [hm1, show 3 * (m / 3) + 1 + 1 = 3 * (m / 3) + 2 by omega, hb1, hb2]
      exact hzero _ hi n hn
    · rw [hm2, show 3 * (m / 3) + 2 + 1 = 3 * (m / 3 + 1) by omega, hb2, hb0]
      exact hafter _ hi n
  have hbprofile : ∀ m < 3 * N, ∀ j : Fin 3,
      Module.finrank ℤ (relativeHomology {x : E // F x ≤ b (m + 1)}
        {x | F x.1 ≤ b m} j.val) = ∑ q ∈ T m, if k q = j then 1 else 0 := by
    intro m hm j
    obtain ⟨hi, hm0 | hm1 | hm2⟩ := hstages m hm
    · rw [hm0, hb0, hb1, ht0, Finset.sum_empty]
      exact hzrank (hbefore _ hi j.val)
    · rw [hm1, show 3 * (m / 3) + 1 + 1 = 3 * (m / 3) + 2 by omega, hb1, hb2, ht1]
      exact hprofile _ hi j
    · rw [hm2, show 3 * (m / 3) + 2 + 1 = 3 * (m / 3 + 1) by omega, hb2, hb0, ht2,
        Finset.sum_empty]
      exact hzrank (hafter _ hi j.val)
  have hTdisjoint : Set.PairwiseDisjoint (↑(Finset.range (3 * N))) T := by
    intro i hi j hj hij
    change Disjoint (T i) (T j)
    by_cases hi1 : i % 3 = 1
    · by_cases hj1 : j % 3 = 1
      · have hiN : i / 3 < N := by have := Finset.mem_range.mp hi; omega
        have hjN : j / 3 < N := by have := Finset.mem_range.mp hj; omega
        have hne : i / 3 ≠ j / 3 := by intro he; apply hij; omega
        simpa only [T, ite_eq_left hi1, ite_eq_left hj1] using
          hdisjoint (Finset.mem_range.mpr hiN) (Finset.mem_range.mpr hjN) hne
      · simp [T, hj1]
    · simp [T, hi1]
  have hTcover : (Finset.range (3 * N)).biUnion T = Z := by
    rw [← hcover]
    ext q
    constructor
    · intro hq
      obtain ⟨m, hm, hqm⟩ := Finset.mem_biUnion.mp hq
      by_cases hm1 : m % 3 = 1
      · have hi : m / 3 < N := by have := Finset.mem_range.mp hm; omega
        exact Finset.mem_biUnion.mpr ⟨m / 3, Finset.mem_range.mpr hi,
          by simpa only [T, ite_eq_left hm1] using hqm⟩
      · simp [T, hm1] at hqm
    · intro hq
      obtain ⟨i, hi, hqi⟩ := Finset.mem_biUnion.mp hq
      exact Finset.mem_biUnion.mpr ⟨3 * i + 1,
        Finset.mem_range.mpr (by have := Finset.mem_range.mp hi; omega),
        by simpa only [ht1] using hqi⟩
  have hbzero0 : b 0 = a 0 := by simpa using hb0 0
  exact actual_full_integral_euler_of_partitioned_sublevel_relative_profiles
    F (3 * N) b T Z k hbmono (by simpa only [hbzero0] using hbottom)
    (by simpa only [hb0] using htop) hbfinite hbzero hbprofile hTdisjoint hTcover

#print axioms windowed_integral_euler_telescope
