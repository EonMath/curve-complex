import CurveComplexGenusTwo.Topology.ActualDerivativeSignEuler.ActualCriticalWindowComponentProductInternal
import CurveComplexGenusTwo.Topology.ActualFiniteSigmaRelativeHomology.ActualFiniteSigmaRelativeHomologyMap

open Set CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz

theorem actual_critical_window_local_union_relative_profile
    {E : Type} [TopologicalSpace E] [T2Space E]
    (F : E → ℝ) (hF : Continuous F) (S : Finset E)
    (k : E → Fin 3) (c : E → OpenPartialHomeomorph E ℂ)
    (ρ : E → ℝ) (v ε : ℝ) (hε : 0 < ε)
    (hvalue : ∀ q ∈ S, F q = v)
    (hρ : ∀ q ∈ S, 0 < ρ q ∧ ε < (ρ q) ^ 2 ∧
      Metric.closedBall (0 : ℂ) (ρ q) ⊆ (c q).target)
    (hd : Set.PairwiseDisjoint (↑S : Set E)
      (fun q => actualCriticalChartRegion (c q) (ρ q)))
    (hnormal : ∀ q ∈ S, ∀ x ∈ (c q).source,
      F x = F q + actualCriticalWindowQuadratic (k q) (c q x)) :
    (∀ n : ℕ, Module.Finite ℤ (relativeHomology
      (actualCriticalWindowLocalUpper F S c ρ v ε)
      (actualCriticalWindowLocalLower F S c ρ v ε) n)) ∧
    (∀ j : Fin 3, Module.finrank ℤ (relativeHomology
      (actualCriticalWindowLocalUpper F S c ρ v ε)
      (actualCriticalWindowLocalLower F S c ρ v ε) j.val) =
      ∑ q ∈ S, if k q = j then 1 else 0) ∧
    ∀ n : ℕ, 3 ≤ n → IsZero (relativeHomology
      (actualCriticalWindowLocalUpper F S c ρ v ε)
      (actualCriticalWindowLocalLower F S c ρ v ε) n) := by
  classical
  let R (q : S) := {x : E | x ∈ actualCriticalChartRegion (c q.val) (ρ q.val) ∧
    F x ≤ v + ε}
  let A (q : S) : Set (R q) := {x | F x.1 ≤ v - ε}
  have hp :
      (∀ n : ℕ, Module.Finite ℤ (∀ q : S, relativeHomology (R q) (A q) n)) ∧
      (∀ j : Fin 3, Module.finrank ℤ (∀ q : S, relativeHomology (R q) (A q) j.val) =
        ∑ q ∈ S, if k q = j then 1 else 0) ∧
      ∀ n : ℕ, 3 ≤ n → IsZero
        (ModuleCat.of ℤ (∀ q : S, relativeHomology (R q) (A q) n)) := by
    run_tac do
      let n := Lean.Name.str (Lean.Name.num
        (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str .anonymous "_private") "CurveComplexGenusTwo") "Topology") "ActualDerivativeSignEuler") "ActualCriticalWindowComponentProductInternal") 0)
          "actual_critical_window_component_product_relative_profiles"
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n)
        $(Lean.mkIdent `F) $(Lean.mkIdent `S) $(Lean.mkIdent `k) $(Lean.mkIdent `c)
        $(Lean.mkIdent `ρ) $(Lean.mkIdent `v) $(Lean.mkIdent `ε) $(Lean.mkIdent `hε)
        $(Lean.mkIdent `hvalue) $(Lean.mkIdent `hρ) $(Lean.mkIdent `hnormal)))
  have hball : ∀ q ∈ S, Metric.closedBall (0 : ℂ) (ρ q) ⊆ (c q).target :=
    fun q hq => (hρ q hq).2.2
  have ht : ∃ (e : (Σ q : S, R q) ≃ₜ actualCriticalWindowLocalUpper F S c ρ v ε)
      (he : ∀ z, (e z : E) = z.2.val),
      ∀ n : ℕ, IsIso (pairRelativeHomologyMap
        {z : Σ q : S, R q | F z.2.val ≤ v - ε}
        (actualCriticalWindowLocalLower F S c ρ v ε)
        ⟨e, e.continuous⟩
        (fun z hz => by simpa only [actualCriticalWindowLocalLower, mem_ofPred_eq,
          ContinuousMap.coe_mk, he z] using hz) n) := by
    run_tac do
      let n := Lean.Name.str (Lean.Name.num
        (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str .anonymous "_private") "CurveComplexGenusTwo") "Topology") "ActualDerivativeSignEuler") "ActualCriticalWindowUnionTopologyInternal") 0)
          "actual_critical_window_local_union_pair_isIso"
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n)
        $(Lean.mkIdent `F) $(Lean.mkIdent `hF) $(Lean.mkIdent `S) $(Lean.mkIdent `c)
        $(Lean.mkIdent `ρ) $(Lean.mkIdent `v) $(Lean.mkIdent `ε)
        $(Lean.mkIdent `hball) $(Lean.mkIdent `hd)))
  obtain ⟨e, he, hi⟩ := ht
  let assembly (n : ℕ) : (∀ q : S, relativeHomology (R q) (A q) n) ≃ₗ[ℤ]
      relativeHomology (actualCriticalWindowLocalUpper F S c ρ v ε)
        (actualCriticalWindowLocalLower F S c ρ v ε) n := by
    let f := pairRelativeHomologyMap
      {z : Σ q : S, R q | F z.2.val ≤ v - ε}
      (actualCriticalWindowLocalLower F S c ρ v ε) ⟨e, e.continuous⟩
      (fun z hz => by simpa only [actualCriticalWindowLocalLower, mem_ofPred_eq,
        ContinuousMap.coe_mk, he z] using hz) n
    letI : IsIso f := hi n
    exact (LinearEquiv.ofBijective
      (actual_finite_sigma_pair_relative_inclusion_sum S (fun q => R q) A n)
      (actual_finite_sigma_pair_relative_inclusion_sum_bijective S (fun q => R q) A n)).trans
        (asIso f).toLinearEquiv
  refine ⟨?_, ?_, ?_⟩
  · intro n
    letI := hp.1 n
    exact Module.Finite.equiv (assembly n)
  · intro j
    exact (assembly j.val).finrank_eq.symm.trans (hp.2.1 j)
  · intro n hn
    letI : Subsingleton (∀ q : S, relativeHomology (R q) (A q) n) :=
      ModuleCat.subsingleton_of_isZero (hp.2.2 n hn)
    letI : Subsingleton (relativeHomology
        (actualCriticalWindowLocalUpper F S c ρ v ε)
        (actualCriticalWindowLocalLower F S c ρ v ε) n) :=
      ⟨fun x y => (assembly n).symm.injective (Subsingleton.elim _ _)⟩
    exact ModuleCat.isZero_of_subsingleton _

#print axioms actual_critical_window_local_union_relative_profile
