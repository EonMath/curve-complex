import CurveComplexGenusTwo.Topology.ActualDerivativeSignEuler.ActualIntegralHandleEulerAlgebra
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.RingTheory.Finiteness.Prod

variable {R : Type} [CommRing R] [IsDomain R]

private theorem integral_finite_prod_finrank
    (M N : Type) [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module.Finite R M] [Module.Finite R N] :
    Module.finrank R (M × N) = Module.finrank R M + Module.finrank R N := by
  have h := actual_integral_finrank_range_add_finrank_ker (LinearMap.fst R M N)
  have hr : (LinearMap.fst R M N).range = ⊤ :=
    LinearMap.range_eq_top.mpr (fun x => ⟨(x, 0), rfl⟩)
  have hk : Module.finrank R (LinearMap.fst R M N).ker = Module.finrank R N := by
    rw [LinearMap.ker_fst]
    exact LinearMap.finrank_range_of_inj
      (show Function.Injective (LinearMap.inr R M N) from fun x y hxy =>
        congrArg Prod.snd hxy)
  rw [hr, finrank_top, hk] at h
  exact h.symm

private theorem integral_finite_pi_finrank
    (ι : Type) [Fintype ι] (M : ι → Type)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, Module.Finite R (M i)] :
    Module.finrank R (∀ i, M i) = ∑ i, Module.finrank R (M i) := by
  classical
  revert M
  refine Fintype.induction_empty_option
    (P := fun α _ => ∀ (M : α → Type) [∀ i, AddCommGroup (M i)]
      [∀ i, Module R (M i)] [∀ i, Module.Finite R (M i)],
      Module.finrank R (∀ i, M i) = ∑ i, Module.finrank R (M i)) ?_ ?_ ?_ ι
  · intro α β _ e ih M _ _ _
    letI : Fintype α := Fintype.ofEquiv β e.symm
    calc
      Module.finrank R (∀ i, M i) = Module.finrank R (∀ i, M (e i)) :=
        (LinearEquiv.piCongrLeft R M e).finrank_eq.symm
      _ = ∑ i, Module.finrank R (M (e i)) := ih (fun i => M (e i))
      _ = ∑ i, Module.finrank R (M i) := e.sum_comp (fun i => Module.finrank R (M i))
  · intro M _ _ _
    simpa using (Module.finrank_zero_of_subsingleton (R := R) (M := ∀ i, M i))
  · intro α _ ih M _ _ _
    rw [(LinearEquiv.piOptionEquivProd R).finrank_eq,
      integral_finite_prod_finrank, ih]
    exact (Fintype.sum_option (fun i => Module.finrank R (M i))).symm

#print axioms integral_finite_prod_finrank
#print axioms integral_finite_pi_finrank
