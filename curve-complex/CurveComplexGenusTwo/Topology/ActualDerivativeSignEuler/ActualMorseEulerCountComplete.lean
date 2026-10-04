import CurveComplexGenusTwo.Topology.ActualDerivativeSignEuler.ActualCriticalWindowLocalUnionProfile
import CurveComplexGenusTwo.Topology.ActualDerivativeSignEuler.ActualRetainedMorseWindowsInternal
import CurveComplexGenusTwo.Topology.ActualDerivativeSignEuler.ActualWindowedEulerTelescopeInternal
import CurveComplexGenusTwo.Topology.ActualDerivativeSignEuler.ActualPartitionedSublevelEuler
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualMorseReferenceZeroSet
import CurveComplexGenusTwo.Topology.ActualSmoothMorseNormalForm.ActualComplexSmoothMorseParity

open scoped Manifold ContDiff Bundle
open Bundle CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz

/-! REVIEW ONLY. Milnor, Morse Theory, §3 Theorem 3.2 and Remark 3.3.
The actual function, critical set, upward field, charts, and indices are retained.
Simultaneous critical values are grouped without assuming distinct values.
The proof consumes the proved actual critical-window inclusion and finite
singular disjoint-union decomposition, then the existing integral telescope.
No relative-profile, index-sum, homology or Euler certificate is an input. -/

theorem actual_smooth_morse_function_full_integral_euler_count
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E] [CompactSpace E] [T2Space E]
    (F : E → ℝ) (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F)
    (Z : Finset E)
    (hcritical : (Z : Set E) = {x | mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x = 0})
    (X : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (hX : ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (X x)))
    (hup : ∀ x : E, x ∉ Z →
      0 < (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F x))
        ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x) (X x)))
    (k : Z → Fin 3) (c : Z → OpenPartialHomeomorph E ℂ)
    (hcenter : ∀ q : Z, q.val ∈ (c q).source ∧ c q q.val = 0)
    (hchart : ∀ q : Z,
      ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ (c q) (c q).source ∧
      ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ (c q).symm (c q).target)
    (hnormal : ∀ q : Z, ∀ x ∈ (c q).source,
      F x = F q.val + actualComplexMorseQuadratic (k q) (c q x)) :
    (∑ q : Z, (-1 : ℤ) ^ (k q : ℕ)) =
      ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
        (Module.finrank ℤ (CurveComplex.integralHomology E n) : ℤ) := by
  classical
  by_cases hZ : Z.Nonempty
  · have hnonempty := hZ
    obtain ⟨q₀, hq₀⟩ := hZ
    let k' : E → Fin 3 := fun q => if hq : q ∈ Z then k ⟨q, hq⟩ else 0
    let c' : E → OpenPartialHomeomorph E ℂ := fun q =>
      if hq : q ∈ Z then c ⟨q, hq⟩ else c ⟨q₀, hq₀⟩
    have hk (q : Z) : k' q.val = k q := by simp [k', q.property]
    have hc (q : Z) : c' q.val = c q := by simp [c', q.property]
    have hcenter' : ∀ q ∈ Z, q ∈ (c' q).source ∧ c' q q = 0 := by
      intro q hq
      simpa only [hc ⟨q, hq⟩] using hcenter ⟨q, hq⟩
    have hchart' : ∀ q ∈ Z,
        ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ (c' q) (c' q).source ∧
        ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ (c' q).symm (c' q).target := by
      intro q hq
      simpa only [hc ⟨q, hq⟩] using hchart ⟨q, hq⟩
    have hnormal' : ∀ q ∈ Z, ∀ x ∈ (c' q).source,
        F x = F q + actualCriticalWindowQuadratic (k' q) (c' q x) := by
      intro q hq
      simpa only [hc ⟨q, hq⟩, hk ⟨q, hq⟩, actualCriticalWindowQuadratic,
        actualComplexMorseQuadratic] using hnormal ⟨q, hq⟩
    have hselected :
      ∃ (N : ℕ) (_ : 0 < N) (v : Fin N ↪o ℝ)
      (S : ℕ → Finset E) (a : ℕ → ℝ) (ε : Fin N → ℝ) (ρ : Fin N → E → ℝ),
      (∀ x, a 0 < F x) ∧ (∀ x, F x < a N) ∧
      Set.PairwiseDisjoint (↑(Finset.range N)) S ∧
      (Finset.range N).biUnion S = Z ∧
      (∀ i : Fin N, ∀ q, q ∈ S i.val ↔ q ∈ Z ∧ F q = v i) ∧
      ∀ i : Fin N,
        0 < ε i ∧ a i.val < v i - ε i ∧ v i + ε i < a (i.val + 1) ∧
        (∀ q ∈ S i.val, 0 < ρ i q ∧ ε i < (ρ i q) ^ 2 ∧
          Metric.closedBall (0 : ℂ) (ρ i q) ⊆ (c' q).target) ∧
        Set.PairwiseDisjoint (↑(S i.val) : Set E)
          (fun q => actualCriticalChartRegion (c' q) (ρ i q)) ∧
        (∀ n : ℕ, IsIso (pairRelativeHomologyMap
          (actualCriticalWindowLocalLower F (S i.val) c' (ρ i) (v i) (ε i))
          (actualCriticalWindowFullLower F (v i) (ε i))
          (actualCriticalWindowInclusion F (S i.val) c' (ρ i) (v i) (ε i))
          (fun _ hx => hx) n)) ∧
        (∀ n : ℕ, IsZero (relativeHomology {x : E // F x ≤ v i - ε i}
          {x | F x.1 ≤ a i.val} n)) ∧
        ∀ n : ℕ, IsZero (relativeHomology {x : E // F x ≤ a (i.val + 1)}
          {x | F x.1 ≤ v i + ε i} n) := by
      run_tac do
        let n := Lean.Name.str (Lean.Name.num
          (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str .anonymous "_private") "CurveComplexGenusTwo") "Topology") "ActualDerivativeSignEuler") "ActualRetainedMorseWindowsInternal") 0) "retained_regular_and_critical_windows"
        Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n)
          $(Lean.mkIdent `F) $(Lean.mkIdent `hF) $(Lean.mkIdent `Z) $(Lean.mkIdent `hnonempty)
          $(Lean.mkIdent `X) $(Lean.mkIdent `hX) $(Lean.mkIdent `hup)
          $(Lean.mkIdent `k') $(Lean.mkIdent `c') $(Lean.mkIdent `hcenter')
          $(Lean.mkIdent `hchart') $(Lean.mkIdent `hnormal')))
    obtain ⟨N, hN, v, S, a, ε, ρ, hbottom, htop, hdisjoint, hcover, hS, hwindow⟩ := hselected
    -- Sole exact residual: the literal finite union of the actual normal-chart pairs.
    -- CRITICAL_LOCAL_UNION_REVIEW_REQUEST.md binds this leaf to the canonical finite-Sigma map.
    have hLocalUnion : ∀ (T : Finset E) (r : E → ℝ) (w δ : ℝ), 0 < δ →
        (∀ q ∈ T, F q = w) →
        (∀ q ∈ T, 0 < r q ∧ δ < (r q) ^ 2 ∧
          Metric.closedBall (0 : ℂ) (r q) ⊆ (c' q).target) →
        Set.PairwiseDisjoint (↑T : Set E)
          (fun q => actualCriticalChartRegion (c' q) (r q)) →
        (∀ q ∈ T, ∀ x ∈ (c' q).source,
          F x = F q + actualCriticalWindowQuadratic (k' q) (c' q x)) →
        (∀ n : ℕ, Module.Finite ℤ (relativeHomology
          (actualCriticalWindowLocalUpper F T c' r w δ)
          (actualCriticalWindowLocalLower F T c' r w δ) n)) ∧
        (∀ j : Fin 3, Module.finrank ℤ (relativeHomology
          (actualCriticalWindowLocalUpper F T c' r w δ)
          (actualCriticalWindowLocalLower F T c' r w δ) j.val) =
          ∑ q ∈ T, if k' q = j then 1 else 0) ∧
        ∀ n : ℕ, 3 ≤ n → IsZero (relativeHomology
          (actualCriticalWindowLocalUpper F T c' r w δ)
          (actualCriticalWindowLocalLower F T c' r w δ) n) := by
      intro T r w δ hδ hvalue hρ hd hn
      exact actual_critical_window_local_union_relative_profile
        F hF.continuous T k' c' r w δ hδ hvalue hρ hd hn
    have hprofiles (i : Fin N) :
        (∀ n : ℕ, Module.Finite ℤ (relativeHomology {x : E // F x ≤ v i + ε i}
          {x | F x.1 ≤ v i - ε i} n)) ∧
        (∀ j : Fin 3, Module.finrank ℤ (relativeHomology {x : E // F x ≤ v i + ε i}
          {x | F x.1 ≤ v i - ε i} j.val) = ∑ q ∈ S i.val, if k' q = j then 1 else 0) ∧
        ∀ n : ℕ, 3 ≤ n → IsZero (relativeHomology {x : E // F x ≤ v i + ε i}
          {x | F x.1 ≤ v i - ε i} n) := by
      obtain ⟨hε, _, _, hr, hd, hcomparison, _, _⟩ := hwindow i
      obtain ⟨hfinite, hrank, hzero⟩ := hLocalUnion (S i.val) (ρ i) (v i) (ε i) hε
        (fun q hq => ((hS i q).mp hq).2) hr hd
        (fun q hq => hnormal' q ((hS i q).mp hq).1)
      have hiso (n : ℕ) := hcomparison n
      constructor
      · intro n
        letI := hiso n
        letI := hfinite n
        exact Module.Finite.equiv (asIso (pairRelativeHomologyMap
          (actualCriticalWindowLocalLower F (S i.val) c' (ρ i) (v i) (ε i))
          (actualCriticalWindowFullLower F (v i) (ε i))
          (actualCriticalWindowInclusion F (S i.val) c' (ρ i) (v i) (ε i))
          (fun _ hx => hx) n)).toLinearEquiv
      constructor
      · intro j
        letI := hiso j.val
        exact (asIso (pairRelativeHomologyMap
          (actualCriticalWindowLocalLower F (S i.val) c' (ρ i) (v i) (ε i))
          (actualCriticalWindowFullLower F (v i) (ε i))
          (actualCriticalWindowInclusion F (S i.val) c' (ρ i) (v i) (ε i))
          (fun _ hx => hx) j.val)).toLinearEquiv.finrank_eq.symm.trans (hrank j)
      · intro n hn
        letI := hiso n
        exact (hzero n hn).of_iso (asIso (pairRelativeHomologyMap
          (actualCriticalWindowLocalLower F (S i.val) c' (ρ i) (v i) (ε i))
          (actualCriticalWindowFullLower F (v i) (ε i))
          (actualCriticalWindowInclusion F (S i.val) c' (ρ i) (v i) (ε i))
          (fun _ hx => hx) n)).symm
    let l : ℕ → ℝ := fun i => if hi : i < N then v ⟨i, hi⟩ - ε ⟨i, hi⟩ else a i
    let u : ℕ → ℝ := fun i => if hi : i < N then v ⟨i, hi⟩ + ε ⟨i, hi⟩ else a i
    have hl (i : Fin N) : l i.val = v i - ε i := by simp [l, i.isLt]
    have hu (i : Fin N) : u i.val = v i + ε i := by simp [u, i.isLt]
    have horder : ∀ i < N, a i ≤ l i ∧ l i ≤ u i ∧ u i ≤ a (i + 1) := by
      intro i hi
      rw [hl ⟨i, hi⟩, hu ⟨i, hi⟩]
      obtain ⟨he, hleft, hright, _⟩ := hwindow ⟨i, hi⟩
      exact ⟨hleft.le, by linarith, hright.le⟩
    have hbefore : ∀ i < N, ∀ n : ℕ,
        IsZero (relativeHomology {x : E // F x ≤ l i} {x | F x.1 ≤ a i} n) := by
      intro i hi n
      rw [hl ⟨i, hi⟩]
      exact (hwindow ⟨i, hi⟩).2.2.2.2.2.2.1 n
    have hafter : ∀ i < N, ∀ n : ℕ,
        IsZero (relativeHomology {x : E // F x ≤ a (i + 1)} {x | F x.1 ≤ u i} n) := by
      intro i hi n
      rw [hu ⟨i, hi⟩]
      exact (hwindow ⟨i, hi⟩).2.2.2.2.2.2.2 n
    have hfinite : ∀ i < N, ∀ n : ℕ,
        Module.Finite ℤ (relativeHomology {x : E // F x ≤ u i} {x | F x.1 ≤ l i} n) := by
      intro i hi n
      rw [hl ⟨i, hi⟩, hu ⟨i, hi⟩]
      exact (hprofiles ⟨i, hi⟩).1 n
    have hzero : ∀ i < N, ∀ n : ℕ, 3 ≤ n →
        IsZero (relativeHomology {x : E // F x ≤ u i} {x | F x.1 ≤ l i} n) := by
      intro i hi n hn
      rw [hl ⟨i, hi⟩, hu ⟨i, hi⟩]
      exact (hprofiles ⟨i, hi⟩).2.2 n hn
    have hprofile : ∀ i < N, ∀ j : Fin 3,
        Module.finrank ℤ (relativeHomology {x : E // F x ≤ u i}
          {x | F x.1 ≤ l i} j.val) = ∑ q ∈ S i, if k' q = j then 1 else 0 := by
      intro i hi j
      rw [hl ⟨i, hi⟩, hu ⟨i, hi⟩]
      exact (hprofiles ⟨i, hi⟩).2.1 j
    have htelescope : (∑ q ∈ Z, (-1 : ℤ) ^ (k' q : ℕ)) =
        ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
          (Module.finrank ℤ (CurveComplex.integralHomology E n) : ℤ) := by
      run_tac do
        let n := Lean.Name.str (Lean.Name.num
          (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str .anonymous "_private") "CurveComplexGenusTwo") "Topology") "ActualDerivativeSignEuler") "ActualWindowedEulerTelescopeInternal") 0) "windowed_integral_euler_telescope"
        Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n)
          $(Lean.mkIdent `F) $(Lean.mkIdent `N) $(Lean.mkIdent `a) $(Lean.mkIdent `l)
          $(Lean.mkIdent `u) $(Lean.mkIdent `S) $(Lean.mkIdent `Z) $(Lean.mkIdent `k')
          $(Lean.mkIdent `hbottom) (fun x => ($(Lean.mkIdent `htop) x).le)
          $(Lean.mkIdent `horder) $(Lean.mkIdent `hbefore) $(Lean.mkIdent `hafter)
          $(Lean.mkIdent `hfinite) $(Lean.mkIdent `hzero) $(Lean.mkIdent `hprofile)
          $(Lean.mkIdent `hdisjoint) $(Lean.mkIdent `hcover)))
    have hsum : (∑ q : Z, (-1 : ℤ) ^ (k q : ℕ)) =
        ∑ q ∈ Z, (-1 : ℤ) ^ (k' q : ℕ) := by
      rw [← Finset.sum_coe_sort Z (fun q => (-1 : ℤ) ^ (k' q : ℕ))]
      apply Finset.sum_congr rfl
      intro q _
      rw [hk q]
    exact hsum.trans htelescope
  · have hempty : Z = ∅ := Finset.not_nonempty_iff_eq_empty.mp hZ
    have hpos : ∀ x : E, 0 < (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F x))
        ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x) (X x)) := by
      intro x
      exact hup x (by simp [hempty])
    have hEuler : (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
        (Module.finrank ℤ (CurveComplex.integralHomology E n) : ℤ)) = 0 := by
      run_tac do
        let n := Lean.Name.str (Lean.Name.num
          (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str .anonymous "_private") "CurveComplexGenusTwo") "Topology") "ActualDerivativeSignEuler") "ActualMorseGeneralRegularGapInternal") 0) "no_retained_critical_points_full_euler_zero"
        Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n)
          $(Lean.mkIdent `F) $(Lean.mkIdent `hF) $(Lean.mkIdent `X) $(Lean.mkIdent `hX)
          $(Lean.mkIdent `hpos)))
    have hsum : (∑ q : Z, (-1 : ℤ) ^ (k q : ℕ)) = 0 := by
      haveI : IsEmpty Z := ⟨fun q => by simpa [hempty] using q.property⟩
      exact Finset.sum_eq_zero (fun q _ => isEmptyElim q)
    exact hsum.trans hEuler.symm
