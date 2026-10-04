import CurveComplexGenusTwo.Topology.ActualDerivativeSignEuler.ActualOrderedCriticalValuesInternal
import CurveComplexGenusTwo.Topology.ActualDerivativeSignEuler.ActualMorseGeneralRegularGapInternal
import CurveComplexGenusTwo.Topology.ActualDerivativeSignEuler.ActualCriticalWindowLocalProfileBridgeInternal

open scoped Manifold ContDiff Bundle
open Bundle Set CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz

private theorem retained_regular_and_critical_windows
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E] [DecidableEq E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E] [CompactSpace E] [T2Space E]
    (F : E → ℝ) (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F)
    (Z : Finset E) (hZ : Z.Nonempty)
    (X : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (hX : ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (X x)))
    (hup : ∀ x : E, x ∉ Z →
      0 < (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F x))
        ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x) (X x)))
    (k : E → Fin 3) (c : E → OpenPartialHomeomorph E ℂ)
    (hcenter : ∀ q ∈ Z, q ∈ (c q).source ∧ c q q = 0)
    (hchart : ∀ q ∈ Z,
      ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ (c q) (c q).source ∧
      ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ (c q).symm (c q).target)
    (hnormal : ∀ q ∈ Z, ∀ x ∈ (c q).source,
      F x = F q + actualCriticalWindowQuadratic (k q) (c q x)) :
    ∃ (N : ℕ) (_ : 0 < N) (v : Fin N ↪o ℝ)
      (S : ℕ → Finset E) (a : ℕ → ℝ) (ε : Fin N → ℝ) (ρ : Fin N → E → ℝ),
      (∀ x, a 0 < F x) ∧ (∀ x, F x < a N) ∧
      Set.PairwiseDisjoint (↑(Finset.range N)) S ∧
      (Finset.range N).biUnion S = Z ∧
      (∀ i : Fin N, ∀ q, q ∈ S i.val ↔ q ∈ Z ∧ F q = v i) ∧
      ∀ i : Fin N,
        0 < ε i ∧ a i.val < v i - ε i ∧ v i + ε i < a (i.val + 1) ∧
        (∀ q ∈ S i.val, 0 < ρ i q ∧ ε i < (ρ i q) ^ 2 ∧
          Metric.closedBall (0 : ℂ) (ρ i q) ⊆ (c q).target) ∧
        Set.PairwiseDisjoint (↑(S i.val) : Set E)
          (fun q => actualCriticalChartRegion (c q) (ρ i q)) ∧
        (∀ n : ℕ, IsIso (pairRelativeHomologyMap
          (actualCriticalWindowLocalLower F (S i.val) c (ρ i) (v i) (ε i))
          (actualCriticalWindowFullLower F (v i) (ε i))
          (actualCriticalWindowInclusion F (S i.val) c (ρ i) (v i) (ε i))
          (fun _ hx => hx) n)) ∧
        (∀ n : ℕ, IsZero (relativeHomology {x : E // F x ≤ v i - ε i}
          {x | F x.1 ≤ a i.val} n)) ∧
        ∀ n : ℕ, IsZero (relativeHomology {x : E // F x ≤ a (i.val + 1)}
          {x | F x.1 ≤ v i + ε i} n) := by
  classical
  obtain ⟨A, B, _, hA, hB⟩ :=
    actual_continuous_compact_scalar_has_strict_endpoint_bounds F hF.continuous
  have horder : ∃ (N : ℕ) (_ : 0 < N) (v : Fin N ↪o ℝ)
      (S : ℕ → Finset E) (a : ℕ → ℝ) (η : Fin N → ℝ),
      a 0 = A ∧ a N = B ∧
      (∀ i (hi : i < N) q, q ∈ S i ↔ q ∈ Z ∧ F q = v ⟨i, hi⟩) ∧
      Set.PairwiseDisjoint (↑(Finset.range N)) S ∧
      (Finset.range N).biUnion S = Z ∧
      (∀ i : Fin N, 0 < η i ∧ a i.val < v i - η i ∧
        v i + η i < a (i.val + 1)) ∧
      (∀ i : Fin N, ∀ q ∈ Z,
        F q ∈ Icc (a i.val) (a (i.val + 1)) ↔ q ∈ S i.val) ∧
      ∀ i : Fin N, ∀ ε : ℝ, 0 < ε → ε < η i →
        (∀ q ∈ Z, F q ∈ Icc (v i - η i) (v i + η i) ↔ q ∈ S i.val) ∧
        (∀ q ∈ Z, F q ∉ Icc (a i.val) (v i - ε)) ∧
        (∀ q ∈ Z, F q ∉ Icc (v i + ε) (a (i.val + 1))) := by
    run_tac do
      let n := Lean.Name.str (Lean.Name.num
        (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str .anonymous "_private") "CurveComplexGenusTwo") "Topology") "ActualDerivativeSignEuler") "ActualOrderedCriticalValuesInternal") 0) "retained_nonempty_critical_value_windows"
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n)
        $(Lean.mkIdent `F) $(Lean.mkIdent `Z) $(Lean.mkIdent `hZ)
        $(Lean.mkIdent `A) $(Lean.mkIdent `B) (fun q _ => $(Lean.mkIdent `hA) q)
        (fun q _ => $(Lean.mkIdent `hB) q)))
  obtain ⟨N, hN, v, S, a, η, ha0, haN, hS, hd, hc, hη, _, hav⟩ := horder
  have hwindow (i : Fin N) : ∃ (ε : ℝ) (ρ : E → ℝ),
      0 < ε ∧ ε < η i ∧
      (∀ q ∈ S i.val, 0 < ρ q ∧ ε < (ρ q) ^ 2 ∧
        Metric.closedBall (0 : ℂ) (ρ q) ⊆ (c q).target) ∧
      Set.PairwiseDisjoint (↑(S i.val) : Set E)
        (fun q => actualCriticalChartRegion (c q) (ρ q)) ∧
      ∀ n : ℕ, IsIso (pairRelativeHomologyMap
        (actualCriticalWindowLocalLower F (S i.val) c ρ (v i) ε)
        (actualCriticalWindowFullLower F (v i) ε)
        (actualCriticalWindowInclusion F (S i.val) c ρ (v i) ε)
        (fun _ hx => hx) n) := by
    apply actual_simultaneous_critical_window_inclusion_relativeHomology_isIso
      F hF X hX (S i.val) (v i) (η i) (hη i).1
      (fun q hq => ((hS i.val i.isLt q).mp hq).2) _ k c
      (fun q hq => hcenter q ((hS i.val i.isLt q).mp hq).1)
      (fun q hq => hchart q ((hS i.val i.isLt q).mp hq).1)
      (fun q hq => hnormal q ((hS i.val i.isLt q).mp hq).1)
    intro x hx hnot
    apply hup x
    intro hxZ
    have hnear := (hav i (η i / 2) (by linarith [(hη i).1])
      (by linarith [(hη i).1])).1 x hxZ
    exact hnot (hnear.mp hx)
  choose ε ρ hε hεη hρ hdis hcomparison using hwindow
  refine ⟨N, hN, v, S, a, ε, ρ, ?_, ?_, hd, hc,
    fun i q => hS i.val i.isLt q, ?_⟩
  · simpa only [ha0] using hA
  · simpa only [haN] using hB
  intro i
  have hl : a i.val < v i - ε i := by linarith [(hη i).2.1, hεη i]
  have hr : v i + ε i < a (i.val + 1) := by linarith [(hη i).2.2, hεη i]
  obtain ⟨_, hbefore, hafter⟩ := hav i (ε i) (hε i) (hεη i)
  refine ⟨hε i, hl, hr, hρ i, hdis i, hcomparison i, ?_, ?_⟩
  · run_tac do
      let n := Lean.Name.str (Lean.Name.num
        (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str .anonymous "_private") "CurveComplexGenusTwo") "Topology") "ActualDerivativeSignEuler") "ActualMorseGeneralRegularGapInternal") 0) "retained_uphill_regular_gap_relative_zero"
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n)
        $(Lean.mkIdent `F) $(Lean.mkIdent `hF) $(Lean.mkIdent `Z) $(Lean.mkIdent `X)
        $(Lean.mkIdent `hX) $(Lean.mkIdent `hup) ($(Lean.mkIdent `a) $(Lean.mkIdent `i).val)
        ($(Lean.mkIdent `v) $(Lean.mkIdent `i) - $(Lean.mkIdent `ε) $(Lean.mkIdent `i))
        $(Lean.mkIdent `hl).le $(Lean.mkIdent `hbefore)))
  · run_tac do
      let n := Lean.Name.str (Lean.Name.num
        (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str .anonymous "_private") "CurveComplexGenusTwo") "Topology") "ActualDerivativeSignEuler") "ActualMorseGeneralRegularGapInternal") 0) "retained_uphill_regular_gap_relative_zero"
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n)
        $(Lean.mkIdent `F) $(Lean.mkIdent `hF) $(Lean.mkIdent `Z) $(Lean.mkIdent `X)
        $(Lean.mkIdent `hX) $(Lean.mkIdent `hup)
        ($(Lean.mkIdent `v) $(Lean.mkIdent `i) + $(Lean.mkIdent `ε) $(Lean.mkIdent `i))
        ($(Lean.mkIdent `a) ($(Lean.mkIdent `i).val + 1))
        $(Lean.mkIdent `hr).le $(Lean.mkIdent `hafter)))

#print axioms retained_regular_and_critical_windows
