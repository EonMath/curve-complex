import CurveComplexGenusTwo.Topology.ActualDerivativeSignEuler.ActualRetainedMorseWindowsInternal
import CurveComplexGenusTwo.Topology.ActualFiniteDiscDetection.FiniteWithSingletonCandidate

open Set CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz

noncomputable section

private theorem actual_critical_window_local_union_homeomorph
    {E : Type} [TopologicalSpace E] [T2Space E]
    (F : E → ℝ) (hF : Continuous F) (S : Finset E)
    (c : E → OpenPartialHomeomorph E ℂ) (ρ : E → ℝ) (v ε : ℝ)
    (hball : ∀ q ∈ S, Metric.closedBall (0 : ℂ) (ρ q) ⊆ (c q).target)
    (hd : Set.PairwiseDisjoint (↑S : Set E)
      (fun q => actualCriticalChartRegion (c q) (ρ q))) :
    ∃ e : (Σ q : S, {x : E | x ∈ actualCriticalChartRegion (c q.val) (ρ q.val) ∧
        F x ≤ v + ε}) ≃ₜ actualCriticalWindowLocalUpper F S c ρ v ε,
      ∀ z, (e z : E) = z.2.val := by
  classical
  let K : S → Set E := fun q =>
    {x | x ∈ actualCriticalChartRegion (c q.val) (ρ q.val) ∧ F x ≤ v + ε}
  have hK (q : S) : IsClosed (K q) := by
    apply IsClosed.inter
    · exact (actual_partial_chart_closed_ball_region_compact
        (c q.val) (ρ q.val) (hball q.val q.property)).isClosed
    · exact isClosed_le hF continuous_const
  have hdis : Set.univ.Pairwise (fun q r : S => Disjoint (K q) (K r)) := by
    intro q _ r _ hqr
    exact (hd q.property r.property (by intro he; exact hqr (Subtype.ext he))).mono
      (fun _ hx => hx.1) (fun _ hx => hx.1)
  let e₀ : (Σ q : S, K q) ≃ₜ (⋃ q : S, K q) := by
    run_tac do
      let n := Lean.Name.str (Lean.Name.num
        (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str .anonymous "_private") "CurveComplexGenusTwo") "Topology") "ActualFiniteDiscDetection") "FiniteWithSingletonCandidate") 0) "actual_finite_disjoint_closed_union_homeomorph"
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n)
        $(Lean.mkIdent `E) $(Lean.mkIdent `S) $(Lean.mkIdent `K)
        $(Lean.mkIdent `hK) $(Lean.mkIdent `hdis)))
  have hset : (⋃ q : S, K q) = actualCriticalWindowLocalUpper F S c ρ v ε := by
    ext x
    simp only [mem_iUnion, K, mem_ofPred_eq, actualCriticalWindowLocalUpper]
    constructor
    · rintro ⟨q, hq, hf⟩
      exact ⟨⟨q.val, q.property, hq⟩, hf⟩
    · rintro ⟨⟨q, hq, hx⟩, hf⟩
      exact ⟨⟨q, hq⟩, hx, hf⟩
  refine ⟨e₀.trans (Homeomorph.setCongr hset), ?_⟩
  intro z
  rfl

private theorem actual_critical_window_local_union_pair_isIso
    {E : Type} [TopologicalSpace E] [T2Space E]
    (F : E → ℝ) (hF : Continuous F) (S : Finset E)
    (c : E → OpenPartialHomeomorph E ℂ) (ρ : E → ℝ) (v ε : ℝ)
    (hball : ∀ q ∈ S, Metric.closedBall (0 : ℂ) (ρ q) ⊆ (c q).target)
    (hd : Set.PairwiseDisjoint (↑S : Set E)
      (fun q => actualCriticalChartRegion (c q) (ρ q))) :
    ∃ (e : (Σ q : S, {x : E | x ∈ actualCriticalChartRegion (c q.val) (ρ q.val) ∧
        F x ≤ v + ε}) ≃ₜ actualCriticalWindowLocalUpper F S c ρ v ε)
      (he : ∀ z, (e z : E) = z.2.val),
      ∀ n : ℕ, IsIso (pairRelativeHomologyMap
        {z : Σ q : S, {x : E | x ∈ actualCriticalChartRegion (c q.val) (ρ q.val) ∧
          F x ≤ v + ε} | F z.2.val ≤ v - ε}
        (actualCriticalWindowLocalLower F S c ρ v ε)
        ⟨e, e.continuous⟩
        (fun z hz => by simpa only [actualCriticalWindowLocalLower, mem_ofPred_eq,
          ContinuousMap.coe_mk, he z] using hz) n) := by
  obtain ⟨e, he⟩ := actual_critical_window_local_union_homeomorph F hF S c ρ v ε hball hd
  refine ⟨e, he, ?_⟩
  intro n
  exact actual_pairRelativeHomologyMap_homeomorph_isIso _ _ _ _ e
    (fun z => by simp only [actualCriticalWindowLocalLower, mem_ofPred_eq, he z]) n

#print axioms actual_critical_window_local_union_homeomorph
#print axioms actual_critical_window_local_union_pair_isIso

private theorem actual_critical_window_component_relative_profiles
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
    ∀ q : S,
      (∀ n : ℕ, Module.Finite ℤ (relativeHomology (R q) (A q) n)) ∧
      (∀ j : Fin 3, Module.finrank ℤ (relativeHomology (R q) (A q) j.val) =
        if k q.val = j then 1 else 0) ∧
      ∀ n : ℕ, 3 ≤ n → IsZero (relativeHomology (R q) (A q) n) := by
  dsimp only
  intro q
  have hh :
      let R := {x : E | x ∈ (c q.val).source ∧ ‖c q.val x‖ ≤ ρ q.val ∧
        F x ≤ F q.val + ε};
      let A : Set R := {x | F x.1 ≤ F q.val - ε};
      (∀ n : ℕ, Module.Finite ℤ (relativeHomology R A n)) ∧
        (∀ j : Fin 3, Module.finrank ℤ (relativeHomology R A j.val) =
          if k q.val = j then 1 else 0) ∧
        ∀ n : ℕ, 3 ≤ n → IsZero (relativeHomology R A n) := by
    have hr := hρ q.val q.property
    have hn := hnormal q.val q.property
    run_tac do
      let n := Lean.Name.str (Lean.Name.num
        (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str .anonymous "_private") "CurveComplexGenusTwo") "Topology") "ActualDerivativeSignEuler") "ActualCriticalWindowLocalProfileBridgeInternal") 0)
          "actual_critical_window_local_normal_chart_profile"
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n)
        ($(Lean.mkIdent `c) $(Lean.mkIdent `q).val) $(Lean.mkIdent `F)
        $(Lean.mkIdent `q).val ($(Lean.mkIdent `k) $(Lean.mkIdent `q).val)
        ($(Lean.mkIdent `ρ) $(Lean.mkIdent `q).val) $(Lean.mkIdent `ε)
        $(Lean.mkIdent `hr).1 $(Lean.mkIdent `hε) $(Lean.mkIdent `hr).2.1
        $(Lean.mkIdent `hr).2.2 $(Lean.mkIdent `hn)))
  rw [hvalue q.val q.property] at hh
  dsimp only at hh
  have hset : {x : E | x ∈ (c q.val).source ∧ ‖c q.val x‖ ≤ ρ q.val ∧ F x ≤ v + ε} =
      {x : E | x ∈ actualCriticalChartRegion (c q.val) (ρ q.val) ∧ F x ≤ v + ε} := by
    ext x
    simp only [actualCriticalChartRegion, mem_ofPred_eq, and_assoc]
  rw [hset] at hh
  exact hh

#print axioms actual_critical_window_component_relative_profiles
