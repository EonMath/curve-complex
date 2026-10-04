import CurveComplexGenusTwo.Topology.ActualDerivativeSignEuler.ActualPartitionedSublevelEuler
import CurveComplexGenusTwo.Topology.ActualSimultaneousCriticalWindow.ActualSimultaneousCriticalWindowComparison
import CurveComplexGenusTwo.Topology.ActualDerivativeSignEuler.ActualMorseRegularBandRelativeHomology
import CurveComplexGenusTwo.Topology.ActualDerivativeSignEuler.ActualMorseRegularIntervalEnlargement
import CurveComplexGenusTwo.Topology.ActualSimultaneousCriticalWindow.ActualMorseCompleteContinuousFlow

open scoped Manifold ContDiff Bundle
open Bundle Set CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz

private theorem retained_uphill_regular_gap_relative_zero
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E] [CompactSpace E] [T2Space E]
    (F : E → ℝ) (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F)
    (Z : Finset E) (X : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (hX : ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (X x)))
    (hup : ∀ x : E, x ∉ Z →
      0 < (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F x))
        ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x) (X x)))
    (a b : ℝ) (hab : a ≤ b) (havoid : ∀ q ∈ Z, F q ∉ Icc a b) :
    ∀ n : ℕ, IsZero (relativeHomology {x : E // F x ≤ b}
      {x | F x.1 ≤ a} n) := by
  obtain ⟨δ, hδ, hwide⟩ :=
    actual_finite_critical_value_regular_closed_interval_enlargement F Z a b hab havoid
  let K := F ⁻¹' Icc (a - δ) (b + δ)
  have hK : IsCompact K := (isClosed_Icc.preimage hF.continuous).isCompact
  have hpos : ∀ x ∈ K, 0 < (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F x))
      ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x) (X x)) := by
    intro x hx
    apply hup x
    intro hxZ
    exact hwide x hxZ hx
  have hnormalized : ∃ u : E → ℝ,
      ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
        (fun x => TotalSpace.mk' ℂ x (u x • X x)) ∧
      (∀ x, 0 ≤ (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F x))
        ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x) (u x • X x))) ∧
      ∀ x ∈ K, (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F x))
        ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x) (u x • X x)) = 1 := by
    run_tac do
      let n := Lean.Name.str (Lean.Name.num
        (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str .anonymous "_private") "CurveComplexGenusTwo") "Topology") "ActualSimultaneousCriticalWindow") "ActualSimultaneousCriticalWindowComparison") 0) "normalize_nonnegative_on_compact"
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n)
        $(Lean.mkIdent `F) $(Lean.mkIdent `hF) $(Lean.mkIdent `X) $(Lean.mkIdent `hX)
        $(Lean.mkIdent `K) $(Lean.mkIdent `hK) $(Lean.mkIdent `hpos)))
  obtain ⟨u, hu, _, hunit⟩ := hnormalized
  obtain ⟨φ, hcurve⟩ := actual_smooth_complex_field_has_global_flow (fun x => u x • X x) hu
  exact actual_normalized_regular_band_relative_homology_zero F hF
    (fun x => u x • X x) φ hcurve (a - δ) a b (b + δ)
    (by linarith) hab (by linarith) hunit

#print axioms retained_uphill_regular_gap_relative_zero

private theorem no_retained_critical_points_full_euler_zero
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E] [CompactSpace E] [T2Space E]
    (F : E → ℝ) (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F)
    (X : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (hX : ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (X x)))
    (hup : ∀ x : E, 0 < (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F x))
      ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x) (X x))) :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      (Module.finrank ℤ (CurveComplex.integralHomology E n) : ℤ)) = 0 := by
  classical
  obtain ⟨a, b, hab, ha, hb⟩ :=
    actual_continuous_compact_scalar_has_strict_endpoint_bounds F hF.continuous
  have hrel := retained_uphill_regular_gap_relative_zero F hF ∅ X hX
    (fun x _ => hup x) a b hab.le (by simp)
  have hzero (n : ℕ) : IsZero (H E n) := by
    have hz := actual_sublevel_integral_H_zero_of_relative_zero F a b hab.le n
      (actual_integral_sublevel_homology_zero_below_function F a ha n) (hrel n)
    exact hz.of_iso (CircleHomologyComputation.homotopyHomologyIso
      (actual_top_sublevel_homeomorph F b (fun x => (hb x).le)).toHomotopyEquiv n).symm
  have hrank (n : ℕ) : Module.finrank ℤ (CurveComplex.integralHomology E n) = 0 := by
    change Module.finrank ℤ (H E n) = 0
    letI := ModuleCat.subsingleton_of_isZero (hzero n)
    exact Module.finrank_zero_of_subsingleton
  simp [hrank]

#print axioms no_retained_critical_points_full_euler_zero
