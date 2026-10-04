import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Analysis.Complex.Basic

open scoped Manifold ContDiff Bundle Topology
open Bundle

theorem actual_literal_tangent_coefficient_smooth
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (W : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (hW : ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (W x))) (q : E) :
    ContDiffAt ℝ 1
      (fun w : ℂ =>
        let x := (chartAt ℂ q).symm ((chartAt ℂ q) q + w)
        (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q
          (TotalSpace.mk' ℂ x (W x))).2) 0 := by
  let e := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q
  let b : E → ℂ := fun x => (e (TotalSpace.mk' ℂ x (W x))).2
  have hq : q ∈ e.baseSet := mem_baseSet_trivializationAt ℂ _ q
  have hbOn : ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ b e.baseSet := by
    exact (e.contMDiffOn_section_baseSet_iff).mp hW.contMDiffOn
  have hbAt : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ b q :=
    (hbOn q hq).contMDiffAt (e.open_baseSet.mem_nhds hq)
  have hbChart := (contMDiffAt_iff_of_mem_source
    (I := 𝓘(ℝ,ℂ)) (I' := 𝓘(ℝ,ℂ)) (n := ∞)
    (mem_chart_source ℂ q) (mem_chart_source ℂ (b q))).mp hbAt
  have hraw : ContDiffAt ℝ ∞ (fun z : ℂ => b ((chartAt ℂ q).symm z))
      ((chartAt ℂ q) q) := by
    simpa only [Function.comp_def, contDiffWithinAt_univ, mfld_simps, extChartAt, OpenPartialHomeomorph.extend,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.id_comp, Function.comp_id] using hbChart.2
  have hshift : ContDiffAt ℝ ∞ (fun w : ℂ => (chartAt ℂ q) q + w) 0 :=
    contDiffAt_const.add contDiffAt_id
  have hraw' : ContDiffAt ℝ ∞ (fun z : ℂ => b ((chartAt ℂ q).symm z))
      ((chartAt ℂ q) q + (0 : ℂ)) := by simpa using hraw
  have hcomp := hraw'.comp 0 hshift
  simpa only [Function.comp_def, add_zero] using hcomp.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
