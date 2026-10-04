import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Analysis.Complex.Basic

open scoped Manifold ContDiff Bundle Topology
open Bundle

theorem actual_tangent_chart_coefficient_contDiffOn
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (W : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (hW : ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (W x))) (q : E) :
    ContDiffOn ℝ 1
      (fun z : ℂ =>
        let x := (chartAt ℂ q).symm z
        (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q
          (TotalSpace.mk' ℂ x (W x))).2)
      (chartAt ℂ q).target := by
  let c := chartAt ℂ q
  let e := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q
  let b : E → ℂ := fun x => (e (TotalSpace.mk' ℂ x (W x))).2
  have hbOn : ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ b e.baseSet :=
    (e.contMDiffOn_section_baseSet_iff).mp hW.contMDiffOn
  intro z hz
  let x := c.symm z
  have hx : x ∈ c.source := c.map_target hz
  have hxe : x ∈ e.baseSet := by simpa [e, c] using hx
  have hbAt : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ b x :=
    (hbOn x hxe).contMDiffAt (e.open_baseSet.mem_nhds hxe)
  have hbChart := (contMDiffAt_iff_of_mem_source
    (I := 𝓘(ℝ,ℂ)) (I' := 𝓘(ℝ,ℂ)) (n := ∞)
    hx (mem_chart_source ℂ (b x))).mp hbAt
  have hraw : ContDiffAt ℝ ∞ (fun w : ℂ => b (c.symm w)) (c x) := by
    simpa only [c, Function.comp_def, contDiffWithinAt_univ, mfld_simps,
      extChartAt, OpenPartialHomeomorph.extend, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id] using hbChart.2
  have hcx : c x = z := c.right_inv hz
  rw [hcx] at hraw
  exact (hraw.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)).contDiffWithinAt

#print axioms actual_tangent_chart_coefficient_contDiffOn
