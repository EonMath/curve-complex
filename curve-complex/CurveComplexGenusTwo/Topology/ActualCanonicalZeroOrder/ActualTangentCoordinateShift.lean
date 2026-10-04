import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Analysis.Complex.Basic

open scoped Manifold ContDiff Bundle Topology
open Bundle

theorem actual_tangent_trivialization_bump_shift
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (q x : E) (hx : x ∈ (chartAt ℂ q).source)
    (W : ∀ y : E, TangentSpace 𝓘(ℝ,ℂ) y)
    (a : ℝ) (c : ℂ) :
    let e := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q;
    (e (TotalSpace.mk' ℂ x (W x + a • e.symmL ℝ x c))).2 =
      (e (TotalSpace.mk' ℂ x (W x))).2 + a • c := by
  let e := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q
  have hbase : x ∈ e.baseSet := by simpa [e] using hx
  change (e ⟨x, W x + a • e.symmL ℝ x c⟩).2 =
    (e ⟨x, W x⟩).2 + a • c
  rw [← e.continuousLinearMapAt_apply_of_mem (R := ℝ) hbase]
  rw [← e.continuousLinearMapAt_apply_of_mem (R := ℝ) hbase]
  simp only [map_add, map_smul, e.continuousLinearMapAt_symmL hbase]

private theorem actual_literal_chart_symm_eventually_in_source
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E] (q : E) :
    ∀ᶠ w : ℂ in 𝓝 (0 : ℂ),
      (chartAt ℂ q).symm ((chartAt ℂ q) q + w) ∈ (chartAt ℂ q).source := by
  let cq := chartAt ℂ q
  have htarget : cq q ∈ cq.target := cq.map_source (mem_chart_source ℂ q)
  have hlim : Filter.Tendsto (fun w : ℂ => cq q + w) (𝓝 (0 : ℂ)) (𝓝 (cq q)) := by
    have hcont : Continuous (fun w : ℂ => cq q + w) := continuous_const.add continuous_id
    have ht : Filter.Tendsto (fun w : ℂ => cq q + w) (𝓝 (0 : ℂ))
        (𝓝 (cq q + 0)) := hcont.continuousAt
    simpa only [add_zero] using ht
  filter_upwards [hlim.eventually (cq.open_target.mem_nhds htarget)] with w hw
  exact cq.map_target hw
