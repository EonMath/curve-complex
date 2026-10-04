import CurveComplexGenusTwo.Topology.ActualSmoothMorseNormalForm.ActualSameAtlasMorseLinearBump
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp

open scoped Manifold ContDiff Topology

theorem actual_smooth_scalar_chart_pullback_contDiffOn
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (p : E) (F : E → ℝ)
    (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F) :
    ContDiffOn ℝ 2 (fun z : ℂ => F ((chartAt ℂ p).symm z))
      (chartAt ℂ p).target := by
  let c := chartAt ℂ p
  intro z hz
  let x := c.symm z
  have hx : x ∈ c.source := c.map_target hz
  have hFAt : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F x := hF.contMDiffAt
  have hFChart := (contMDiffAt_iff_of_mem_source
    (I := 𝓘(ℝ,ℂ)) (I' := 𝓘(ℝ)) (n := ∞)
    hx (mem_chart_source ℝ (F x))).mp hFAt
  have hraw : ContDiffAt ℝ ∞ (fun w : ℂ => F (c.symm w)) (c x) := by
    simpa only [c, Function.comp_def, contDiffWithinAt_univ, mfld_simps,
      extChartAt, OpenPartialHomeomorph.extend, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id] using
      hFChart.2
  have hcx : c x = z := c.right_inv hz
  rw [hcx] at hraw
  exact (hraw.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ ∞)).contDiffWithinAt

#print axioms actual_smooth_scalar_chart_pullback_contDiffOn

theorem actual_smooth_scalar_chart_pullback_contDiffOn_infty
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (p : E) (F : E → ℝ)
    (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F) :
    ContDiffOn ℝ ∞ (fun z : ℂ => F ((chartAt ℂ p).symm z))
      (chartAt ℂ p).target := by
  let c := chartAt ℂ p
  intro z hz
  let x := c.symm z
  have hx : x ∈ c.source := c.map_target hz
  have hFAt : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F x := hF.contMDiffAt
  have hFChart := (contMDiffAt_iff_of_mem_source
    (I := 𝓘(ℝ,ℂ)) (I' := 𝓘(ℝ)) (n := ∞)
    hx (mem_chart_source ℝ (F x))).mp hFAt
  have hraw : ContDiffAt ℝ ∞ (fun w : ℂ => F (c.symm w)) (c x) := by
    simpa only [c, Function.comp_def, contDiffWithinAt_univ, mfld_simps,
      extChartAt, OpenPartialHomeomorph.extend, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id] using
      hFChart.2
  rw [c.right_inv hz] at hraw
  exact hraw.contDiffWithinAt

#print axioms actual_smooth_scalar_chart_pullback_contDiffOn_infty

theorem actual_smooth_scalar_chart_gradient_contDiffOn_infty
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (p : E) (F : E → ℝ)
    (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F) :
    ContDiffOn ℝ ∞
      (gradient (fun z : ℂ => F ((chartAt ℂ p).symm z)))
      (chartAt ℂ p).target := by
  let f : ℂ → ℝ := fun z => F ((chartAt ℂ p).symm z)
  have hfder : ContDiffOn ℝ ∞ (fderiv ℝ f) (chartAt ℂ p).target :=
    (actual_smooth_scalar_chart_pullback_contDiffOn_infty p F hF).fderiv_of_isOpen
      (chartAt ℂ p).open_target (by simp)
  change ContDiffOn ℝ ∞
    (fun z => (InnerProductSpace.toDual ℝ ℂ).symm (fderiv ℝ f z))
    (chartAt ℂ p).target
  exact ((InnerProductSpace.toDual ℝ ℂ).symm.toContinuousLinearMap.contDiff.contDiffOn
    (s := Set.univ)).comp hfder (by simp)

#print axioms actual_smooth_scalar_chart_gradient_contDiffOn_infty
