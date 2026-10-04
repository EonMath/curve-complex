import CurveComplexGenusTwo.Topology.ActualDerivativeSignEuler.ActualCriticalWindowUnionTopologyInternal
import CurveComplexGenusTwo.Topology.ActualDerivativeSignEuler.ActualFiniteIntegralPiRankInternal

open Set CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz

private theorem actual_critical_window_component_product_relative_profiles
    {E : Type} [TopologicalSpace E]
    (F : E → ℝ) (S : Finset E)
    (k : E → Fin 3) (c : E → OpenPartialHomeomorph E ℂ)
    (ρ : E → ℝ) (v ε : ℝ) (hε : 0 < ε)
    (hvalue : ∀ q ∈ S, F q = v)
    (hρ : ∀ q ∈ S, 0 < ρ q ∧ ε < (ρ q) ^ 2 ∧
      Metric.closedBall (0 : ℂ) (ρ q) ⊆ (c q).target)
    (hnormal : ∀ q ∈ S, ∀ x ∈ (c q).source,
      F x = F q + actualCriticalWindowQuadratic (k q) (c q x)) :
    let R (q : S) := {x : E | x ∈ actualCriticalChartRegion (c q.val) (ρ q.val) ∧
      F x ≤ v + ε};
    let A (q : S) : Set (R q) := {x | F x.1 ≤ v - ε};
    (∀ n : ℕ, Module.Finite ℤ (∀ q : S, relativeHomology (R q) (A q) n)) ∧
    (∀ j : Fin 3, Module.finrank ℤ (∀ q : S, relativeHomology (R q) (A q) j.val) =
      ∑ q ∈ S, if k q = j then 1 else 0) ∧
    ∀ n : ℕ, 3 ≤ n → IsZero
      (ModuleCat.of ℤ (∀ q : S, relativeHomology (R q) (A q) n)) := by
  classical
  dsimp only
  let R (q : S) := {x : E | x ∈ actualCriticalChartRegion (c q.val) (ρ q.val) ∧
    F x ≤ v + ε}
  let A (q : S) : Set (R q) := {x | F x.1 ≤ v - ε}
  have hcomp : ∀ q : S,
      (∀ n : ℕ, Module.Finite ℤ (relativeHomology (R q) (A q) n)) ∧
      (∀ j : Fin 3, Module.finrank ℤ (relativeHomology (R q) (A q) j.val) =
        if k q.val = j then 1 else 0) ∧
      ∀ n : ℕ, 3 ≤ n → IsZero (relativeHomology (R q) (A q) n) := by
    run_tac do
      let n := Lean.Name.str (Lean.Name.num
        (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str .anonymous "_private") "CurveComplexGenusTwo") "Topology") "ActualDerivativeSignEuler") "ActualCriticalWindowUnionTopologyInternal") 0) "actual_critical_window_component_relative_profiles"
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n)
        $(Lean.mkIdent `F) $(Lean.mkIdent `S) $(Lean.mkIdent `k) $(Lean.mkIdent `c)
        $(Lean.mkIdent `ρ) $(Lean.mkIdent `v) $(Lean.mkIdent `ε) $(Lean.mkIdent `hε)
        $(Lean.mkIdent `hvalue) $(Lean.mkIdent `hρ) $(Lean.mkIdent `hnormal)))
  have hfinite (n : ℕ) : Module.Finite ℤ (∀ q : S, relativeHomology (R q) (A q) n) := by
    letI : ∀ q : S, Module.Finite ℤ (relativeHomology (R q) (A q) n) :=
      fun q => (hcomp q).1 n
    have hmod : Pi.module S (fun q => relativeHomology (R q) (A q) n) ℤ =
        AddCommGroup.toIntModule (∀ q : S, relativeHomology (R q) (A q) n) :=
      Subsingleton.elim _ _
    rw [← hmod]
    infer_instance
  refine ⟨hfinite, ?_, ?_⟩
  · intro j
    let M : S → Type := fun q => relativeHomology (R q) (A q) j.val
    letI : ∀ q : S, Module.Finite ℤ (M q) := fun q => (hcomp q).1 j.val
    have hmod : Pi.module S M ℤ = AddCommGroup.toIntModule (∀ q : S, M q) :=
      Subsingleton.elim _ _
    have hp : Module.finrank ℤ (∀ q : S, M q) = ∑ q : S, Module.finrank ℤ (M q) := by
      rw [← hmod]
      run_tac do
        let n := Lean.Name.str (Lean.Name.num
          (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str .anonymous "_private") "CurveComplexGenusTwo") "Topology") "ActualDerivativeSignEuler") "ActualFiniteIntegralPiRankInternal") 0) "integral_finite_pi_finrank"
        Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n)
          (R := ℤ) $(Lean.mkIdent `S) $(Lean.mkIdent `M)))
    calc
      Module.finrank ℤ (∀ q : S, relativeHomology (R q) (A q) j.val) =
          ∑ q : S, Module.finrank ℤ (relativeHomology (R q) (A q) j.val) := hp
      _ = ∑ q : S, if k q.val = j then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro q _
        exact (hcomp q).2.1 j
      _ = ∑ q ∈ S, if k q = j then 1 else 0 := Finset.sum_coe_sort S (fun q => if k q = j then (1 : ℕ) else 0)
  · intro n hn
    letI : ∀ q : S, Subsingleton (relativeHomology (R q) (A q) n) :=
      fun q => ModuleCat.subsingleton_of_isZero ((hcomp q).2.2 n hn)
    exact ModuleCat.isZero_of_subsingleton _

#print axioms actual_critical_window_component_product_relative_profiles
