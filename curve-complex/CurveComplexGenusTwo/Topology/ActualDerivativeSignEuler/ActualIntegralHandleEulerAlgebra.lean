import Mathlib.Algebra.Exact.Sequence
import Mathlib.LinearAlgebra.Dimension.Localization

open Function
open Module

variable {R : Type*} [CommRing R] [IsDomain R]

theorem actual_integral_finrank_range_add_finrank_ker
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module.Finite R M]
    (f : M →ₗ[R] N) :
    Module.finrank R f.range + Module.finrank R f.ker = Module.finrank R M := by
  have h := f.ker.finrank_quotient_add_finrank
  rw [f.quotKerEquivRange.finrank_eq] at h
  exact h

theorem actual_integral_sum_neg_one_pow_finrank_eq_zero_of_exact
    {n : ℕ} (V : Fin (n + 2) → Type*)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, Module.Finite R (V i)]
    (f : (i : Fin (n + 1)) → V i.castSucc →ₗ[R] V i.succ)
    (hfirst : Injective (f 0))
    (hexact : ∀ i : Fin n, Exact (f i.castSucc) (f i.succ))
    (hlast : Surjective (f (Fin.last n))) :
    ∑ i, (-1 : ℤ) ^ i.val * (Module.finrank R (V i) : ℤ) = 0 := by
  have hinj : Module.finrank R (f 0).range = Module.finrank R (V 0) :=
    LinearMap.finrank_range_of_inj hfirst
  have hsurj := LinearMap.range_eq_top.mpr hlast
  simp_rw [← smul_eq_mul]
  refine Fin.sum_neg_one_pow_eq_zero _
    (fun i => (Module.finrank R (f i).range : ℤ)) ?_ (fun i => ?_) ?_
  · exact congrArg (fun a : ℕ => (a : ℤ)) hinj.symm
  · have hrn := actual_integral_finrank_range_add_finrank_ker (f i.succ)
    have hker : Module.finrank R (f i.succ).ker =
        Module.finrank R (f i.castSucc).range :=
      congrArg (fun S : Submodule R (V i.succ.castSucc) => Module.finrank R S)
        (hexact i).linearMap_ker_eq
    omega
  · rw [hsurj, finrank_top, Fin.succ_last]

theorem actual_integral_euler_additivity_of_ten_term_exact_sequence
    (V : Fin 10 → Type*)
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℤ (V i)]
    [∀ i, Module.Finite ℤ (V i)]
    (f : (i : Fin 9) → V i.castSucc →ₗ[ℤ] V i.succ)
    (hfirst : Injective (f 0))
    (hexact : ∀ i : Fin 8, Exact (f i.castSucc) (f i.succ))
    (hlast : Surjective (f (Fin.last 8))) :
    (Module.finrank ℤ (V 7) : ℤ) - Module.finrank ℤ (V 4) +
      Module.finrank ℤ (V 1) =
    (Module.finrank ℤ (V 6) : ℤ) - Module.finrank ℤ (V 3) +
      Module.finrank ℤ (V 0) +
      Module.finrank ℤ (V 8) - Module.finrank ℤ (V 5) +
      Module.finrank ℤ (V 2) - Module.finrank ℤ (V 9) := by
  have h := actual_integral_sum_neg_one_pow_finrank_eq_zero_of_exact
    V f hfirst hexact hlast
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at h
  dsimp [Fin.succ] at h
  norm_num at h
  omega

theorem actual_finite_morse_index_sign_sum
    {I : Type*} (S : Finset I) (k : I → Fin 3) :
    (∑ i ∈ S, (-1 : ℤ) ^ (k i : ℕ)) =
      (∑ i ∈ S, if k i = 0 then (1 : ℤ) else 0) -
      (∑ i ∈ S, if k i = 1 then (1 : ℤ) else 0) +
      (∑ i ∈ S, if k i = 2 then (1 : ℤ) else 0) := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  generalize h : k i = ki
  fin_cases ki <;> norm_num

theorem actual_integral_finite_event_euler_telescoping
    (N : ℕ) (χ c : ℕ → ℤ)
    (hstep : ∀ i < N, χ (i + 1) = χ i + c i) :
    χ N = χ 0 + ∑ i ∈ Finset.range N, c i := by
  induction N with
  | zero => simp
  | succ n ih =>
      have hprev : ∀ i < n, χ (i + 1) = χ i + c i :=
        fun i hi => hstep i (Nat.lt_succ_of_lt hi)
      rw [hstep n (Nat.lt_succ_self n), ih hprev, Finset.sum_range_succ]
      ring
