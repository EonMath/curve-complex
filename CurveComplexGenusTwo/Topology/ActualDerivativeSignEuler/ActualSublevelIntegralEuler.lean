import CurveComplexGenusTwo.Topology.ActualDerivativeSignEuler.ActualPairIntegralEulerAdditivity
import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseHelpers

open Function Set CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz

def actual_nested_sublevel_homeomorph
    {E : Type} [TopologicalSpace E] (F : E → ℝ)
    (a b : ℝ) (hab : a ≤ b) :
    {x : {x : E // F x ≤ b} // F x.1 ≤ a} ≃ₜ {x : E // F x ≤ a} where
  toFun x := ⟨x.1.1, x.2⟩
  invFun x := ⟨⟨x.1, x.2.trans hab⟩, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

theorem actual_nested_sublevel_integral_H_finrank
    {E : Type} [TopologicalSpace E] (F : E → ℝ)
    (a b : ℝ) (hab : a ≤ b) (n : ℕ) :
    Module.finrank ℤ
      (H ({x : {x : E // F x ≤ b} | F x.1 ≤ a} : Set {x : E // F x ≤ b}) n) =
    Module.finrank ℤ (H {x : E // F x ≤ a} n) := by
  let i := CircleHomologyComputation.homotopyHomologyIso
    (actual_nested_sublevel_homeomorph F a b hab).toHomotopyEquiv n
  exact i.toLinearEquiv.finrank_eq

theorem actual_nested_sublevel_integral_H_finite
    {E : Type} [TopologicalSpace E] (F : E → ℝ)
    (a b : ℝ) (hab : a ≤ b) (n : ℕ)
    [Module.Finite ℤ (H {x : E // F x ≤ a} n)] :
    Module.Finite ℤ
      (H ({x : {x : E // F x ≤ b} | F x.1 ≤ a} : Set {x : E // F x ≤ b}) n) := by
  let i := CircleHomologyComputation.homotopyHomologyIso
    (actual_nested_sublevel_homeomorph F a b hab).toHomotopyEquiv n
  exact Module.Finite.equiv i.toLinearEquiv.symm

theorem actual_sublevel_integral_H_finite_of_relative_finite
    {E : Type} [TopologicalSpace E] (F : E → ℝ)
    (a b : ℝ) (hab : a ≤ b) (n : ℕ)
    [Module.Finite ℤ (H {x : E // F x ≤ a} n)]
    [Module.Finite ℤ (relativeHomology {x : E // F x ≤ b} {x | F x.1 ≤ a} n)] :
    Module.Finite ℤ (H {x : E // F x ≤ b} n) := by
  letI := actual_nested_sublevel_integral_H_finite F a b hab n
  exact actual_H_finite_of_subspace_and_relative_finite
    {x : E // F x ≤ b} {x | F x.1 ≤ a} n

theorem actual_sublevel_integral_H_zero_of_relative_zero
    {E : Type} [TopologicalSpace E] (F : E → ℝ)
    (a b : ℝ) (hab : a ≤ b) (n : ℕ)
    (hA : IsZero (H {x : E // F x ≤ a} n))
    (hR : IsZero (relativeHomology {x : E // F x ≤ b} {x | F x.1 ≤ a} n)) :
    IsZero (H {x : E // F x ≤ b} n) := by
  have hAz := hA.of_iso (CircleHomologyComputation.homotopyHomologyIso
    (actual_nested_sublevel_homeomorph F a b hab).toHomotopyEquiv n)
  exact actual_H_zero_of_subspace_and_relative_zero
    {x : E // F x ≤ b} {x | F x.1 ≤ a} n hAz hR

theorem actual_sublevel_integral_euler_increment_of_finite_relative_profile
    {E : Type} [TopologicalSpace E] (F : E → ℝ)
    (a b : ℝ) (hab : a ≤ b)
    [Module.Finite ℤ (H {x : E // F x ≤ a} 0)]
    [Module.Finite ℤ (H {x : E // F x ≤ a} 1)]
    [Module.Finite ℤ (H {x : E // F x ≤ a} 2)]
    [Module.Finite ℤ (relativeHomology {x : E // F x ≤ b} {x | F x.1 ≤ a} 0)]
    [Module.Finite ℤ (relativeHomology {x : E // F x ≤ b} {x | F x.1 ≤ a} 1)]
    [Module.Finite ℤ (relativeHomology {x : E // F x ≤ b} {x | F x.1 ≤ a} 2)]
    (hthree : IsZero (relativeHomology {x : E // F x ≤ b} {x | F x.1 ≤ a} 3))
    {I : Type*} (S : Finset I) (k : I → Fin 3)
    (hr0 : Module.finrank ℤ
      (relativeHomology {x : E // F x ≤ b} {x | F x.1 ≤ a} 0) =
      ∑ i ∈ S, if k i = 0 then 1 else 0)
    (hr1 : Module.finrank ℤ
      (relativeHomology {x : E // F x ≤ b} {x | F x.1 ≤ a} 1) =
      ∑ i ∈ S, if k i = 1 then 1 else 0)
    (hr2 : Module.finrank ℤ
      (relativeHomology {x : E // F x ≤ b} {x | F x.1 ≤ a} 2) =
      ∑ i ∈ S, if k i = 2 then 1 else 0) :
    (Module.finrank ℤ (H {x : E // F x ≤ b} 0) : ℤ) -
      Module.finrank ℤ (H {x : E // F x ≤ b} 1) +
      Module.finrank ℤ (H {x : E // F x ≤ b} 2) =
    (Module.finrank ℤ (H {x : E // F x ≤ a} 0) : ℤ) -
      Module.finrank ℤ (H {x : E // F x ≤ a} 1) +
      Module.finrank ℤ (H {x : E // F x ≤ a} 2) + ∑ i ∈ S, (-1 : ℤ) ^ (k i : ℕ) := by
  letI := actual_nested_sublevel_integral_H_finite F a b hab 0
  letI := actual_nested_sublevel_integral_H_finite F a b hab 1
  letI := actual_nested_sublevel_integral_H_finite F a b hab 2
  have h := actual_pair_integral_euler_increment_of_finite_relative_profile
    {x : E // F x ≤ b} {x | F x.1 ≤ a} hthree S k hr0 hr1 hr2
  simpa only [actual_nested_sublevel_integral_H_finrank F a b hab] using h
