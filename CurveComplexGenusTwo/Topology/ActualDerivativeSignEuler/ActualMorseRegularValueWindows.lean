import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualMorseFiniteCriticalSet
import Mathlib.Topology.MetricSpace.Basic

open Set Topology

theorem actual_finite_critical_value_regular_window
    {E : Type*} (F : E → ℝ) (Z : Finset E)
    (c : ℝ) (hc : ∀ x ∈ Z, F x ≠ c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Z, δ ≤ |F x - c| := by
  let S : Set ℝ := F '' (Z : Set E)
  have hSfinite : S.Finite := Z.finite_toSet.image F
  have hSclosed : IsClosed S := hSfinite.isClosed
  have hnot : c ∈ Sᶜ := by
    intro hmem
    obtain ⟨x, hx, hxc⟩ := hmem
    exact hc x hx hxc
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hSclosed.isOpen_compl c hnot
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  by_contra hbad
  have hnear : F x ∈ Metric.ball c δ := by
    simpa only [Metric.mem_ball, Real.dist_eq] using (lt_of_not_ge hbad)
  have hFnot : F x ∈ Sᶜ := hball hnear
  exact hFnot ⟨x, hx, rfl⟩
