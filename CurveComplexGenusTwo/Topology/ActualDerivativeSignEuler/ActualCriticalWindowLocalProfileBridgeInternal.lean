import CurveComplexGenusTwo.Topology.ActualSimultaneousCriticalWindow.ActualSimultaneousCriticalWindowComparison
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualAllMorseLocalProfilesInternal
import CurveComplexGenusTwo.Topology.ActualSmoothMorseNormalForm.ActualComplexSmoothMorseParity

open CategoryTheory CategoryTheory.Limits Set
open CurveComplexGenusTwo.CWHurewicz

private theorem actual_critical_window_quadratic_eq_morse_quadratic
    (k : Fin 3) (z : ℂ) :
    actualCriticalWindowQuadratic k z = actualComplexMorseQuadratic k z := by
  rfl

private theorem actual_critical_window_local_normal_chart_profile
    {E : Type} [TopologicalSpace E] (c : OpenPartialHomeomorph E ℂ)
    (F : E → ℝ) (p : E) (k : Fin 3) (ρ ε : ℝ)
    (hρ : 0 < ρ) (hε : 0 < ε) (hεr : ε < ρ ^ 2)
    (hball : Metric.closedBall (0 : ℂ) ρ ⊆ c.target)
    (hnormal : ∀ x ∈ c.source, F x = F p + actualCriticalWindowQuadratic k (c x)) :
    let R := {x : E | x ∈ c.source ∧ ‖c x‖ ≤ ρ ∧ F x ≤ F p + ε};
    let A : Set R := {x | F x.1 ≤ F p - ε};
    (∀ n : ℕ, Module.Finite ℤ (relativeHomology R A n)) ∧
      (∀ j : Fin 3, Module.finrank ℤ (relativeHomology R A j.val) = if k = j then 1 else 0) ∧
      ∀ n : ℕ, 3 ≤ n → IsZero (relativeHomology R A n) := by
  have hn : ∀ x ∈ c.source, F x = F p + actualComplexMorseQuadratic k (c x) := by
    simpa only [actual_critical_window_quadratic_eq_morse_quadratic] using hnormal
  have hminus : -(ρ ^ 2) ≤ -ε := by linarith
  have ha : -ε < 0 := neg_neg_of_pos hε
  have hh :
      let R := {x : E | x ∈ c.source ∧ ‖c x‖ ≤ ρ ∧ F x ≤ F p + ε};
      let A : Set R := {x | F x.1 ≤ F p + (-ε)};
      (∀ n : ℕ, Module.Finite ℤ (relativeHomology R A n)) ∧
        (∀ j : Fin 3, Module.finrank ℤ (relativeHomology R A j.val) = if k = j then 1 else 0) ∧
        ∀ n : ℕ, 3 ≤ n → IsZero (relativeHomology R A n) := by
    run_tac do
      let n := Lean.Name.str (Lean.Name.num
        (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str .anonymous "_private") "CurveComplexGenusTwo") "Topology") "ActualMorseEulerExports") "ActualAllMorseLocalProfilesInternal") 0)
        "actual_all_morse_normal_chart_profiles"
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n)
        $(Lean.mkIdent `c) $(Lean.mkIdent `F) $(Lean.mkIdent `p) $(Lean.mkIdent `k)
        $(Lean.mkIdent `ρ) (- $(Lean.mkIdent `ε)) $(Lean.mkIdent `ε)
        $(Lean.mkIdent `hρ) $(Lean.mkIdent `hminus) $(Lean.mkIdent `ha)
        $(Lean.mkIdent `hε).le $(Lean.mkIdent `hball) $(Lean.mkIdent `hn)))
  dsimp only
  have hset :
      {x : {x : E | x ∈ c.source ∧ ‖c x‖ ≤ ρ ∧ F x ≤ F p + ε} | F x.1 ≤ F p - ε} =
      {x : {x : E | x ∈ c.source ∧ ‖c x‖ ≤ ρ ∧ F x ≤ F p + ε} | F x.1 ≤ F p + (-ε)} := by
    ext x
    simp only [sub_eq_add_neg]
  rw [hset]
  exact hh

#print axioms actual_critical_window_quadratic_eq_morse_quadratic
#print axioms actual_critical_window_local_normal_chart_profile
#print axioms actual_simultaneous_critical_window_inclusion_relativeHomology_isIso
