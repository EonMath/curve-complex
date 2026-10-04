import CurveComplexGenusTwo.Topology.ActualCanonicalZeroOrder.ActualOpenCoreRegularization
import CurveComplexGenusTwo.Topology.ActualCanonicalZeroOrder.ActualTangentChartCoefficientOn
import CurveComplexGenusTwo.Topology.ActualCanonicalZeroOrder.ActualBumpChartPullback
import CurveComplexGenusTwo.Topology.ActualCanonicalZeroOrder.ActualTangentCoordinateShift
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Calculus.FDeriv.Congr

open scoped Manifold ContDiff Bundle Topology
open Bundle Set Filter

theorem actual_one_core_tangent_regularization
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [T2Space E] [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (q : E) (bump : SmoothBumpFunction 𝓘(ℝ,ℂ) q)
    (W : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (hW : ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (W x)))
    (r : ℝ) (hr : 0 < r) :
    ∃ c : ℂ, ‖c‖ < r ∧
      ∀ x : E, bump x = 1 →
        (W x + bump x •
          (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q).symmL ℝ x c) = 0 →
        (fderiv ℝ
          (fun z : ℂ =>
            let y := (chartAt ℂ q).symm z
            (trivializationAt ℂ (fun u : E => TangentSpace 𝓘(ℝ,ℂ) u) q
              (TotalSpace.mk' ℂ y (W y + bump y •
                (trivializationAt ℂ (fun u : E => TangentSpace 𝓘(ℝ,ℂ) u) q).symmL ℝ y c))).2)
          ((chartAt ℂ q) x)).det ≠ 0 := by
  let chart := chartAt ℂ q
  let e := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q
  let f : ℂ → ℂ := fun z =>
    (e (TotalSpace.mk' ℂ (chart.symm z) (W (chart.symm z)))).2
  let φ : ℂ → ℝ := fun z => bump (chart.symm z)
  let K : Set ℂ := {z | z ∈ chart.target ∧ φ z = 1}
  have hchart : ContDiffOn ℝ 1 f chart.target :=
    actual_tangent_chart_coefficient_contDiffOn W hW q
  have hφchart : ContDiffOn ℝ 1 φ chart.target :=
    actual_smooth_bump_chart_pullback_contDiffOn q bump
  have hφbound : ∀ z, φ z ≤ 1 := fun z => bump.le_one
  have hKU : K ⊆ chart.target := fun z hz => hz.1
  have hKφ : ∀ z ∈ K, φ z = 1 := fun z hz => hz.2
  have hφdiff : ∀ z ∈ K, DifferentiableAt ℝ φ z := by
    intro z hz
    exact ((hφchart z hz.1).contDiffAt (chart.open_target.mem_nhds hz.1)).differentiableAt
      (by norm_num)
  obtain ⟨c, hc, hreg⟩ := actual_open_bumped_core_regularization
    f chart.target chart.open_target hchart φ hφbound K hKU hKφ hφdiff r hr
  refine ⟨c, hc, ?_⟩
  intro x hx hzero
  have hxsource : x ∈ chart.source :=
    bump.support_subset_source (by simp [hx] : x ∈ Function.support bump)
  let z := chart x
  have hz : z ∈ chart.target := chart.map_source hxsource
  have hzinK : z ∈ K := by
    refine ⟨hz, ?_⟩
    change bump (chart.symm (chart x)) = 1
    rw [chart.left_inv hxsource]
    exact hx
  have hzero' : f z + φ z • c = 0 := by
    have hshift := actual_tangent_trivialization_bump_shift q x hxsource W (bump x) c
    have hval : (e (TotalSpace.mk' ℂ x (W x + bump x • e.symmL ℝ x c))).2 = 0 := by
      have hbase : x ∈ e.baseSet := by simpa [e] using hxsource
      rw [← e.continuousLinearMapAt_apply_of_mem (R := ℝ) hbase, hzero, map_zero]
    change (e (TotalSpace.mk' ℂ x (W x + bump x • e.symmL ℝ x c))).2 =
      (e (TotalSpace.mk' ℂ x (W x))).2 + bump x • c at hshift
    have hxchart : chart.symm z = x := chart.left_inv hxsource
    change (e (TotalSpace.mk' ℂ (chart.symm z) (W (chart.symm z)))).2 +
      bump (chart.symm z) • c = 0
    rw [hxchart]
    exact hshift.symm.trans hval
  let v' : ℂ → ℂ := fun z =>
    let y := chart.symm z
    (e (TotalSpace.mk' ℂ y (W y + bump y • e.symmL ℝ y c))).2
  have hEq : ∀ z ∈ chart.target, v' z = f z + φ z • c := by
    intro w hw
    have hwsource : chart.symm w ∈ chart.source := chart.map_target hw
    exact actual_tangent_trivialization_bump_shift q (chart.symm w) hwsource
      W (bump (chart.symm w)) c
  have hderiv : fderiv ℝ v' z = fderiv ℝ (fun w => f w + φ w • c) z := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [chart.open_target.mem_nhds hz] with w hw
    exact hEq w hw
  simpa only [v'] using (hderiv ▸ hreg z hzinK hzero')

#print axioms actual_one_core_tangent_regularization
