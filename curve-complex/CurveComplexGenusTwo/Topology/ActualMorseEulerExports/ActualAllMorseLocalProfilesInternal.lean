import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualMinimumChartRelativeProfile
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualSaddleNormalChartRelativeProfile
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualMaximumProfileInternal
import CurveComplexGenusTwo.Topology.ActualSmoothMorseNormalForm.ActualComplexSmoothMorseParity

open CategoryTheory CategoryTheory.Limits Set
open CurveComplexGenusTwo.CWHurewicz

private theorem actual_all_morse_normal_chart_profiles
    {E : Type} [TopologicalSpace E] (c : OpenPartialHomeomorph E ℂ)
    (F : E → ℝ) (p : E) (k : Fin 3) (ρ a b : ℝ)
    (hρ : 0 < ρ) (hminus : -(ρ ^ 2) ≤ a) (ha : a < 0) (hb : 0 ≤ b)
    (hball : Metric.closedBall (0 : ℂ) ρ ⊆ c.target)
    (hnormal : ∀ x ∈ c.source, F x = F p + actualComplexMorseQuadratic k (c x)) :
    let R := {x : E | x ∈ c.source ∧ ‖c x‖ ≤ ρ ∧ F x ≤ F p + b};
    let A : Set R := {x | F x.1 ≤ F p + a};
    (∀ n : ℕ, Module.Finite ℤ (relativeHomology R A n)) ∧
      (∀ j : Fin 3, Module.finrank ℤ (relativeHomology R A j.val) = if k = j then 1 else 0) ∧
      ∀ n : ℕ, 3 ≤ n → IsZero (relativeHomology R A n) := by
  dsimp only
  let R := {x : E | x ∈ c.source ∧ ‖c x‖ ≤ ρ ∧ F x ≤ F p + b}
  let A : Set R := {x | F x.1 ≤ F p + a}
  have hnorm (z : ℂ) : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hzeroRank (n : ℕ) (hz : IsZero (relativeHomology R A n)) :
      Module.finrank ℤ (relativeHomology R A n) = 0 := by
    letI := ModuleCat.subsingleton_of_isZero hz
    exact Module.finrank_zero_of_subsingleton
  fin_cases k
  · have hn : ∀ x ∈ c.source, F x = F p + ‖c x‖ ^ 2 := by
      simpa [actualComplexMorseQuadratic, hnorm] using hnormal
    obtain ⟨⟨e0⟩, hp⟩ := actual_minimum_normal_chart_relative_profile c F p ρ a b
      hρ.le ha hb hball hn
    refine ⟨?_, ?_, fun n hn => hp n (by omega)⟩
    · intro n
      cases n with
      | zero => exact Module.Finite.equiv e0.toLinearEquiv.symm
      | succ n =>
          letI := ModuleCat.subsingleton_of_isZero (hp (n + 1) (by omega))
          infer_instance
    · intro j
      fin_cases j
      · change Module.finrank ℤ (relativeHomology R A 0) = 1
        rw [e0.toLinearEquiv.finrank_eq]
        simp
      · exact hzeroRank 1 (hp 1 (by omega))
      · exact hzeroRank 2 (hp 2 (by omega))
  · have hn : ∀ x ∈ c.source, F x = F p + ((c x).re ^ 2 - (c x).im ^ 2) := by
      simpa [actualComplexMorseQuadratic] using hnormal
    obtain ⟨h0, h1, hh, hf⟩ := actual_saddle_normal_chart_relative_profile c F p ρ a b
      hρ hminus ha hb hball hn
    refine ⟨hf, ?_, ?_⟩
    · intro j
      fin_cases j
      · exact hzeroRank 0 h0
      · exact h1
      · exact hzeroRank 2 (hh 0)
    · intro n hn
      obtain ⟨m, hm⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      rw [hm]
      exact hh m
  · have hn : ∀ x ∈ c.source, F x = F p - ‖c x‖ ^ 2 := by
      simpa [actualComplexMorseQuadratic, hnorm, sub_eq_add_neg] using hnormal
    have hp :
        IsZero (relativeHomology R A 0) ∧ IsZero (relativeHomology R A 1) ∧
          Nonempty (relativeHomology R A 2 ≅ ModuleCat.of ℤ ℤ) ∧
          (∀ n : ℕ, 3 ≤ n → IsZero (relativeHomology R A n)) ∧
          ∀ n : ℕ, Module.Finite ℤ (relativeHomology R A n) := by
      run_tac do
        let n := Lean.Name.str (Lean.Name.num
          (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str .anonymous "_private") "CurveComplexGenusTwo") "Topology") "ActualMorseEulerExports") "ActualMaximumProfileInternal") 0)
          "maximum_normal_chart_profile"
        Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n)
          $(Lean.mkIdent `c) $(Lean.mkIdent `F) $(Lean.mkIdent `p)
          $(Lean.mkIdent `ρ) $(Lean.mkIdent `a) $(Lean.mkIdent `b)
          $(Lean.mkIdent `hρ) $(Lean.mkIdent `hminus) $(Lean.mkIdent `ha) $(Lean.mkIdent `hb)
          $(Lean.mkIdent `hball) $(Lean.mkIdent `hn)))
    obtain ⟨h0, h1, ⟨e2⟩, hh, hf⟩ := hp
    refine ⟨hf, ?_, hh⟩
    intro j
    fin_cases j
    · exact hzeroRank 0 h0
    · exact hzeroRank 1 h1
    · change Module.finrank ℤ (relativeHomology R A 2) = 1
      rw [e2.toLinearEquiv.finrank_eq]
      simp

