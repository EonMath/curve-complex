import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualSublevelEulerEndpoints
import CurveComplexGenusTwo.Topology.ActualDerivativeSignEuler.ActualSublevelEulerTelescope

open CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz

theorem actual_integral_sublevel_homology_zero_below_function
    {E : Type} [TopologicalSpace E] (F : E → ℝ) (a : ℝ)
    (ha : ∀ x : E, a < F x) (n : ℕ) :
    IsZero (H {x : E // F x ≤ a} n) := by
  letI : IsEmpty {x : E // F x ≤ a} := ⟨fun x => (not_lt_of_ge x.2) (ha x.1)⟩
  exact actual_integral_singular_homology_zero_of_isEmpty _ n

def actual_top_sublevel_homeomorph
    {E : Type} [TopologicalSpace E] (F : E → ℝ) (b : ℝ)
    (hb : ∀ x : E, F x ≤ b) : {x : E // F x ≤ b} ≃ₜ E where
  toFun := Subtype.val
  invFun x := ⟨x, hb x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

theorem actual_full_integral_euler_eq_top_sublevel
    {E : Type} [TopologicalSpace E] (F : E → ℝ) (b : ℝ)
    (hb : ∀ x : E, F x ≤ b) :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank ℤ (H E n) : ℤ)) =
      (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
        (Module.finrank ℤ (H {x : E // F x ≤ b} n) : ℤ)) := by
  congr 1
  funext n
  let e := CircleHomologyComputation.homotopyHomologyIso
    (actual_top_sublevel_homeomorph F b hb).toHomotopyEquiv n
  rw [e.toLinearEquiv.finrank_eq]

theorem actual_full_integral_euler_of_sublevel_relative_profiles
    {E : Type} [TopologicalSpace E] (F : E → ℝ)
    (N : ℕ) (a : ℕ → ℝ) {I : Type*} (S : ℕ → Finset I) (k : I → Fin 3)
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
        {x | F x.1 ≤ a i} (j : ℕ)) = ∑ q ∈ S i, if k q = j then 1 else 0) :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank ℤ (H E n) : ℤ)) =
      ∑ i ∈ Finset.range N, ∑ q ∈ S i, (-1 : ℤ) ^ (k q : ℕ) := by
  rw [actual_full_integral_euler_eq_top_sublevel F (a N) htop]
  exact actual_sublevel_full_integral_euler_telescope_of_finite_relative_profiles
    F N a S k ha (actual_integral_sublevel_homology_zero_below_function F (a 0) hbottom)
      hfinite hzero hprofile
