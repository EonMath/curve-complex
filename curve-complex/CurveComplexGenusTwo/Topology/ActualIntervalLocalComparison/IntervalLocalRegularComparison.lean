import CurveComplexGenusTwo.Topology.ActualIntervalLocalComparison.IntervalLocalRegularSoundness
import CurveComplexGenusTwo.Topology.ActualIntervalLocalComparison.NormalizedRegularComparison

open scoped Manifold ContDiff Bundle Simplicial
open CanonicalDimensionTwo

namespace CanonicalDimensionTwo

noncomputable def intervalLocalParallelRegularChartTriangle {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (γ δ : ActualRegularPath E)
    (hγs : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ.toFun t ∈ (chartAt ℂ q).source)
    (hγb : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (chartAt ℂ q) (γ.toFun t) ∈ Metric.ball c r)
    (hδs : ∀ t ∈ Set.Icc (0 : ℝ) 1, δ.toFun t ∈ (chartAt ℂ q).source)
    (hδb : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (chartAt ℂ q) (δ.toFun t) ∈ Metric.ball c r)
    (h0 : γ.toFun 0 = δ.toFun 0)
    (h1 : γ.toFun 1 = δ.toFun 1) :
    IntervalLocalRegularChartTriangle E where
  edge01 := γ
  edge12 := δ.reverse
  edge20 := ActualRegularPath.const (γ.toFun 0)
  chartCenter := q
  ballCenter := c
  radius := r
  edge_source := by
    intro η hη t ht
    rcases hη with h | h | h
    · subst η
      exact hγs t ht
    · subst η
      exact hδs (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
    · subst η
      exact hγs 0 (by norm_num)
  edge_ball := by
    intro η hη t ht
    rcases hη with h | h | h
    · subst η
      exact hγb t ht
    · subst η
      exact hδb (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
    · subst η
      exact hγb 0 (by norm_num)
  ball_target := htarget
  endpoint01 := by
    change γ.toFun 1 = δ.toFun (1 - 0)
    simpa using h1
  endpoint12 := by
    change δ.toFun (1 - 1) = γ.toFun 0
    simpa using h0.symm
  endpoint20 := rfl

theorem intervalLocalParallelRegularDifference_mem_normalized {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (γ δ : ActualRegularPath E)
    (hγs : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ.toFun t ∈ (chartAt ℂ q).source)
    (hγb : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (chartAt ℂ q) (γ.toFun t) ∈ Metric.ball c r)
    (hδs : ∀ t ∈ Set.Icc (0 : ℝ) 1, δ.toFun t ∈ (chartAt ℂ q).source)
    (hδb : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (chartAt ℂ q) (δ.toFun t) ∈ Metric.ball c r)
    (h0 : γ.toFun 0 = δ.toFun 0)
    (h1 : γ.toFun 1 = δ.toFun 1) :
    actualParallelRegularDifferenceCycle γ δ h0 h1 ∈
      intervalLocalNormalizedRelations (E := E) := by
  let Δ := intervalLocalParallelRegularChartTriangle q c r htarget γ δ
    hγs hγb hδs hδb h0 h1
  have htriangle : intervalLocalRegularTwoBoundaryToCycles
      (Finsupp.single Δ 1) ∈ intervalLocalNormalizedRelations (E := E) :=
    Submodule.subset_span (Or.inl (Or.inl (Or.inl ⟨Finsupp.single Δ 1, rfl⟩)))
  have hreverse : actualRegularReverseCycle δ ∈
      intervalLocalNormalizedRelations (E := E) :=
    Submodule.subset_span (Or.inl (Or.inr ⟨δ, rfl⟩))
  have hconstant : actualRegularConstantCycle (γ.toFun 0) ∈
      intervalLocalNormalizedRelations (E := E) :=
    Submodule.subset_span (Or.inl (Or.inl (Or.inr ⟨γ.toFun 0, rfl⟩)))
  have heq : actualParallelRegularDifferenceCycle γ δ h0 h1 =
      intervalLocalRegularTwoBoundaryToCycles (Finsupp.single Δ 1) -
        actualRegularReverseCycle δ -
        actualRegularConstantCycle (γ.toFun 0) := by
    apply Subtype.ext
    simp [actualParallelRegularDifferenceCycle,
      intervalLocalRegularTwoBoundaryToCycles,
      intervalLocalRegularTwoBoundary,
      actualRegularReverseCycle, actualRegularConstantCycle, Δ,
      intervalLocalParallelRegularChartTriangle]
    abel
  rw [heq]
  exact (intervalLocalNormalizedRelations (E := E)).sub_mem
    ((intervalLocalNormalizedRelations (E := E)).sub_mem htriangle hreverse)
    hconstant

noncomputable def actualRegularChartTriangle_toIntervalLocal {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (Δ : ActualRegularChartTriangle E) : IntervalLocalRegularChartTriangle E where
  edge01 := Δ.edge01
  edge12 := Δ.edge12
  edge20 := Δ.edge20
  chartCenter := Δ.chartCenter
  ballCenter := Δ.ballCenter
  radius := Δ.radius
  edge_source := fun γ hγ t _ => Δ.edge_source γ hγ t
  edge_ball := fun γ hγ t _ => Δ.edge_ball γ hγ t
  ball_target := Δ.ball_target
  endpoint01 := Δ.endpoint01
  endpoint12 := Δ.endpoint12
  endpoint20 := Δ.endpoint20

theorem actualRegularChartTriangle_intervalLocal_boundary {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (Δ : ActualRegularChartTriangle E) :
    actualRegularChartTwoBoundaryToCycles (Finsupp.single Δ 1) =
      intervalLocalRegularTwoBoundaryToCycles
        (Finsupp.single (actualRegularChartTriangle_toIntervalLocal Δ) 1) := by
  apply Subtype.ext
  simp [actualRegularChartTwoBoundaryToCycles, actualRegularChartTwoBoundary,
    intervalLocalRegularTwoBoundaryToCycles, intervalLocalRegularTwoBoundary,
    actualRegularChartTriangle_toIntervalLocal]

theorem actualNormalizedRelationSet_subset_intervalLocal {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    actualNormalizedRelationSet (E := E) ⊆
      intervalLocalNormalizedRelations (E := E) := by
  intro z hz
  simp only [actualNormalizedRelationSet, Set.mem_union] at hz
  rcases hz with (((h | h) | h) | h)
  · obtain ⟨c, rfl⟩ := h
    have hsum : ∀ d : ActualRegularChartTwoChains E,
        actualRegularChartTwoBoundaryToCycles d ∈
          intervalLocalNormalizedRelations (E := E) := by
      intro d
      induction d using Finsupp.induction with
      | zero => exact (intervalLocalNormalizedRelations (E := E)).zero_mem
      | single_add Δ n d hΔ hd ih =>
          rw [map_add]
          have hsingle : Finsupp.single Δ n = n • (Finsupp.single Δ 1 :
              ActualRegularChartTwoChains E) := by simp
          rw [hsingle, map_smul]
          have hgen : intervalLocalRegularTwoBoundaryToCycles
              (Finsupp.single (actualRegularChartTriangle_toIntervalLocal Δ) 1) ∈
              intervalLocalNormalizedRelations (E := E) :=
            Submodule.subset_span
              (Or.inl (Or.inl (Or.inl
                ⟨Finsupp.single (actualRegularChartTriangle_toIntervalLocal Δ) 1, rfl⟩)))
          have hsingle_mem : actualRegularChartTwoBoundaryToCycles
              (Finsupp.single Δ 1) ∈ intervalLocalNormalizedRelations (E := E) := by
            rw [actualRegularChartTriangle_intervalLocal_boundary]
            exact hgen
          exact (intervalLocalNormalizedRelations (E := E)).add_mem
            ((intervalLocalNormalizedRelations (E := E)).smul_mem n
              hsingle_mem)
            ih
    exact hsum c
  · obtain ⟨x, rfl⟩ := h
    exact Submodule.subset_span (Or.inl (Or.inl (Or.inr ⟨x, rfl⟩)))
  · obtain ⟨γ, rfl⟩ := h
    exact Submodule.subset_span (Or.inl (Or.inr ⟨γ, rfl⟩))
  · obtain ⟨γ, rfl⟩ := h
    exact Submodule.subset_span (Or.inr ⟨γ, rfl⟩)

theorem actualNormalizedRelations_le_intervalLocal {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    actualNormalizedRelations (E := E) ≤
      intervalLocalNormalizedRelations (E := E) := by
  exact Submodule.span_le.mpr actualNormalizedRelationSet_subset_intervalLocal

theorem actualRegularDyadicDifference_mem_intervalLocal {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (k : ℕ) (γ : ActualRegularPath E) :
    actualRegularDyadicDifferenceCycle k γ ∈
      intervalLocalNormalizedRelations (E := E) :=
  actualNormalizedRelations_le_intervalLocal
    (actualRegularDyadicDifference_mem_normalized k γ)

theorem intervalLocalParallelRegularDifference_eq_zero {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (γ δ : ActualRegularPath E)
    (hγs : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ.toFun t ∈ (chartAt ℂ q).source)
    (hγb : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (chartAt ℂ q) (γ.toFun t) ∈ Metric.ball c r)
    (hδs : ∀ t ∈ Set.Icc (0 : ℝ) 1, δ.toFun t ∈ (chartAt ℂ q).source)
    (hδb : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (chartAt ℂ q) (δ.toFun t) ∈ Metric.ball c r)
    (h0 : γ.toFun 0 = δ.toFun 0)
    (h1 : γ.toFun 1 = δ.toFun 1) :
    (intervalLocalNormalizedRelations (E := E)).mkQ
      (actualParallelRegularDifferenceCycle γ δ h0 h1) = 0 := by
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (intervalLocalParallelRegularDifference_mem_normalized q c r htarget
      γ δ hγs hγb hδs hδb h0 h1)

theorem actualRegularDyadicDifference_intervalLocal_eq_zero {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (k : ℕ) (γ : ActualRegularPath E) :
    (intervalLocalNormalizedRelations (E := E)).mkQ
      (actualRegularDyadicDifferenceCycle k γ) = 0 := by
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (actualRegularDyadicDifference_mem_intervalLocal k γ)

end CanonicalDimensionTwo
