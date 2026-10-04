import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Complex.Basic

open scoped Manifold ContDiff Topology

theorem actual_smooth_bump_chart_pullback_contDiffOn
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [T2Space E] [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (q : E) (f : SmoothBumpFunction 𝓘(ℝ,ℂ) q) :
    ContDiffOn ℝ 1 (fun z : ℂ => f ((chartAt ℂ q).symm z))
      (chartAt ℂ q).target := by
  let c := chartAt ℂ q
  intro z hz
  let x := c.symm z
  have hx : x ∈ c.source := c.map_target hz
  have hbAt : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ) ∞ (fun x : E => f x) x :=
    f.contMDiff.contMDiffAt
  have hbChart := (contMDiffAt_iff_of_mem_source
    (I := 𝓘(ℝ,ℂ)) (I' := 𝓘(ℝ,ℝ)) (n := ∞)
    hx (mem_chart_source ℝ (f x))).mp hbAt
  have hraw : ContDiffAt ℝ ∞ (fun w : ℂ => f (c.symm w)) (c x) := by
    simpa only [c, Function.comp_def, contDiffWithinAt_univ, mfld_simps,
      extChartAt, OpenPartialHomeomorph.extend, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id] using hbChart.2
  have hcx : c x = z := c.right_inv hz
  rw [hcx] at hraw
  exact (hraw.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)).contDiffWithinAt

#print axioms actual_smooth_bump_chart_pullback_contDiffOn
