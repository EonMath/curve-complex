import CurveComplexGenusTwo.Topology.ActualIntervalLocalComparison.NormalizedRegularSoundness

open scoped Manifold ContDiff Bundle Simplicial
open CanonicalDimensionTwo
open CurveComplexGenusTwo.CWHurewicz

namespace CanonicalDimensionTwo

noncomputable def actualParallelRegularChartTriangle {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (γ δ : ActualRegularPath E)
    (hγs : ∀ t, γ.toFun t ∈ (chartAt ℂ q).source)
    (hγb : ∀ t, (chartAt ℂ q) (γ.toFun t) ∈ Metric.ball c r)
    (hδs : ∀ t, δ.toFun t ∈ (chartAt ℂ q).source)
    (hδb : ∀ t, (chartAt ℂ q) (δ.toFun t) ∈ Metric.ball c r)
    (h0 : γ.toFun 0 = δ.toFun 0)
    (h1 : γ.toFun 1 = δ.toFun 1) :
    ActualRegularChartTriangle E where
  edge01 := γ
  edge12 := δ.reverse
  edge20 := ActualRegularPath.const (γ.toFun 0)
  chartCenter := q
  ballCenter := c
  radius := r
  edge_source := by
    intro η hη t
    rcases hη with h | h | h
    · subst η
      exact hγs t
    · subst η
      exact hδs (1 - t)
    · subst η
      exact hγs 0
  edge_ball := by
    intro η hη t
    rcases hη with h | h | h
    · subst η
      exact hγb t
    · subst η
      exact hδb (1 - t)
    · subst η
      exact hγb 0
  ball_target := htarget
  endpoint01 := by
    change γ.toFun 1 = δ.toFun (1 - 0)
    simpa using h1
  endpoint12 := by
    change δ.toFun (1 - 1) = γ.toFun 0
    simpa using h0.symm
  endpoint20 := rfl

noncomputable def actualParallelRegularDifferenceCycle {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (γ δ : ActualRegularPath E)
    (h0 : γ.toFun 0 = δ.toFun 0)
    (h1 : γ.toFun 1 = δ.toFun 1) : ActualRegularOneCycles E :=
  ⟨Finsupp.single γ 1 - Finsupp.single δ 1, by
    change actualRegularChainBoundary _ = 0
    rw [map_sub, actualRegularChainBoundary_single,
      actualRegularChainBoundary_single, h0, h1]
    abel⟩

theorem actualParallelRegularDifference_mem_normalized {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (γ δ : ActualRegularPath E)
    (hγs : ∀ t, γ.toFun t ∈ (chartAt ℂ q).source)
    (hγb : ∀ t, (chartAt ℂ q) (γ.toFun t) ∈ Metric.ball c r)
    (hδs : ∀ t, δ.toFun t ∈ (chartAt ℂ q).source)
    (hδb : ∀ t, (chartAt ℂ q) (δ.toFun t) ∈ Metric.ball c r)
    (h0 : γ.toFun 0 = δ.toFun 0)
    (h1 : γ.toFun 1 = δ.toFun 1) :
    actualParallelRegularDifferenceCycle γ δ h0 h1 ∈
      actualNormalizedRelations (E := E) := by
  let Δ := actualParallelRegularChartTriangle q c r htarget γ δ
    hγs hγb hδs hδb h0 h1
  have htriangle : actualRegularChartTwoBoundaryToCycles
      (Finsupp.single Δ 1) ∈ actualNormalizedRelations (E := E) :=
    Submodule.subset_span (Or.inl (Or.inl (Or.inl ⟨Finsupp.single Δ 1, rfl⟩)))
  have hreverse : actualRegularReverseCycle δ ∈
      actualNormalizedRelations (E := E) :=
    Submodule.subset_span (Or.inl (Or.inr ⟨δ, rfl⟩))
  have hconstant : actualRegularConstantCycle (γ.toFun 0) ∈
      actualNormalizedRelations (E := E) :=
    Submodule.subset_span (Or.inl (Or.inl (Or.inr ⟨γ.toFun 0, rfl⟩)))
  have heq : actualParallelRegularDifferenceCycle γ δ h0 h1 =
      actualRegularChartTwoBoundaryToCycles (Finsupp.single Δ 1) -
        actualRegularReverseCycle δ -
        actualRegularConstantCycle (γ.toFun 0) := by
    apply Subtype.ext
    simp [actualParallelRegularDifferenceCycle,
      actualRegularChartTwoBoundaryToCycles,
      actualRegularChartTwoBoundary,
      actualRegularReverseCycle, actualRegularConstantCycle, Δ,
      actualParallelRegularChartTriangle]
    abel
  rw [heq]
  exact (actualNormalizedRelations (E := E)).sub_mem
    ((actualNormalizedRelations (E := E)).sub_mem htriangle hreverse)
    hconstant

theorem actualParallelRegularDifference_eq_zero {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (γ δ : ActualRegularPath E)
    (hγs : ∀ t, γ.toFun t ∈ (chartAt ℂ q).source)
    (hγb : ∀ t, (chartAt ℂ q) (γ.toFun t) ∈ Metric.ball c r)
    (hδs : ∀ t, δ.toFun t ∈ (chartAt ℂ q).source)
    (hδb : ∀ t, (chartAt ℂ q) (δ.toFun t) ∈ Metric.ball c r)
    (h0 : γ.toFun 0 = δ.toFun 0)
    (h1 : γ.toFun 1 = δ.toFun 1) :
    (actualNormalizedRelations (E := E)).mkQ
      (actualParallelRegularDifferenceCycle γ δ h0 h1) = 0 := by
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (actualParallelRegularDifference_mem_normalized q c r htarget
      γ δ hγs hγb hδs hδb h0 h1)

noncomputable def actualRegularDyadicChain {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (k : ℕ) (γ : ActualRegularPath E) : ActualRegularOneChains E :=
  match k with
  | 0 => Finsupp.single γ 1
  | k + 1 =>
      actualRegularDyadicChain k γ.leftHalf +
        actualRegularDyadicChain k γ.rightHalf

theorem actualRegularDyadicChain_boundary {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (k : ℕ) (γ : ActualRegularPath E) :
    actualRegularChainBoundary (actualRegularDyadicChain k γ) =
      actualRegularChainBoundary (Finsupp.single γ 1) := by
  induction k generalizing γ with
  | zero => rfl
  | succ k ih =>
      change actualRegularChainBoundary
          (actualRegularDyadicChain k γ.leftHalf +
            actualRegularDyadicChain k γ.rightHalf) = _
      rw [map_add, ih γ.leftHalf, ih γ.rightHalf]
      have h := actualRegularSubdivision_boundary_zero γ
      rw [map_sub, map_sub] at h
      apply eq_of_sub_eq_zero
      calc
        _ = -(actualRegularChainBoundary (Finsupp.single γ 1) -
          actualRegularChainBoundary (Finsupp.single γ.leftHalf 1) -
          actualRegularChainBoundary (Finsupp.single γ.rightHalf 1)) := by abel
        _ = 0 := by rw [h]; simp

noncomputable def actualRegularDyadicDifferenceCycle {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (k : ℕ) (γ : ActualRegularPath E) : ActualRegularOneCycles E :=
  ⟨Finsupp.single γ 1 - actualRegularDyadicChain k γ, by
    change actualRegularChainBoundary _ = 0
    rw [map_sub, actualRegularDyadicChain_boundary]
    abel⟩

theorem actualRegularDyadicDifference_mem_normalized {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (k : ℕ) (γ : ActualRegularPath E) :
    actualRegularDyadicDifferenceCycle k γ ∈
      actualNormalizedRelations (E := E) := by
  induction k generalizing γ with
  | zero =>
      have hz : actualRegularDyadicDifferenceCycle 0 γ = 0 := by
        apply Subtype.ext
        simp [actualRegularDyadicDifferenceCycle, actualRegularDyadicChain]
      rw [hz]
      exact (actualNormalizedRelations (E := E)).zero_mem
  | succ k ih =>
      have hroot : actualRegularSubdivisionCycle γ ∈
          actualNormalizedRelations (E := E) :=
        Submodule.subset_span (Or.inr ⟨γ, rfl⟩)
      have hsum := (actualNormalizedRelations (E := E)).add_mem
        hroot ((actualNormalizedRelations (E := E)).add_mem
          (ih γ.leftHalf) (ih γ.rightHalf))
      convert hsum using 1
      apply Subtype.ext
      change Finsupp.single γ 1 -
          (actualRegularDyadicChain k γ.leftHalf +
            actualRegularDyadicChain k γ.rightHalf) =
        (Finsupp.single γ 1 - Finsupp.single γ.leftHalf 1 -
          Finsupp.single γ.rightHalf 1) +
        ((Finsupp.single γ.leftHalf 1 -
            actualRegularDyadicChain k γ.leftHalf) +
          (Finsupp.single γ.rightHalf 1 -
            actualRegularDyadicChain k γ.rightHalf))
      abel

theorem actualRegularDyadicChain_period {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (k : ℕ) (γ : ActualRegularPath E) :
    actualRegularChainIntegral s (actualRegularDyadicChain k γ) =
      actualPathIntegral s γ.toFun := by
  have h := actualNormalizedRelations_period_zero s
    (actualRegularDyadicDifference_mem_normalized k γ)
  change actualRegularChainIntegral s
    (Finsupp.single γ 1 - actualRegularDyadicChain k γ) = 0 at h
  rw [map_sub, actualRegularChainIntegral_single, sub_eq_zero] at h
  exact h.symm

noncomputable def actualRegularDyadicSingularFiller {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (k : ℕ) (γ : ActualRegularPath E) :
    (TopCat.toSSet.obj (TopCat.of E)) _⦋2⦌ →₀ ℤ :=
  match k with
  | 0 => 0
  | k + 1 =>
      Finsupp.single (actualRegularSubdivisionSimplex γ) (-1) +
        actualRegularDyadicSingularFiller k γ.leftHalf +
        actualRegularDyadicSingularFiller k γ.rightHalf

theorem actualRegularDyadicSingularFiller_boundary {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (k : ℕ) (γ : ActualRegularPath E) :
    singularBoundaryFinsupp (TopCat.of E) 1
      (actualRegularDyadicSingularFiller k γ) =
      Finsupp.single (actualRegularPathAsSingular γ) 1 -
        actualRegularChainsToSingular (actualRegularDyadicChain k γ) := by
  induction k generalizing γ with
  | zero =>
      simp [actualRegularDyadicSingularFiller, actualRegularDyadicChain,
        actualRegularChainsToSingular, Finsupp.lmapDomain_apply]
  | succ k ih =>
      change singularBoundaryFinsupp (TopCat.of E) 1
        (Finsupp.single (actualRegularSubdivisionSimplex γ) (-1) +
          actualRegularDyadicSingularFiller k γ.leftHalf +
          actualRegularDyadicSingularFiller k γ.rightHalf) = _
      rw [map_add, map_add, actualRegularSubdivisionSimplex_boundary,
        ih γ.leftHalf, ih γ.rightHalf]
      change _ = Finsupp.single (actualRegularPathAsSingular γ) 1 -
        actualRegularChainsToSingular
          (actualRegularDyadicChain k γ.leftHalf +
            actualRegularDyadicChain k γ.rightHalf)
      rw [map_add]
      abel

end CanonicalDimensionTwo
