import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Analysis.Complex.Basic
open scoped Manifold ContDiff Bundle
open Bundle Filter Set Topology
set_option backward.isDefEq.respectTransparency false
section
variable {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
  [IsManifold 𝓘(ℂ) ∞ E] [IsManifold 𝓘(ℝ,ℂ) ∞ E]
private theorem actual_same_atlas_real_complex_tangent_coordinates
    (q x : E) (hx : x ∈ (chartAt ℂ q).source)
    (v : TangentSpace 𝓘(ℂ) x) :
    (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ, ℂ) y) q
      (TotalSpace.mk' ℂ x ((tangentSpaceCastModel 𝓘(ℝ, ℂ) x).symm
        ((tangentSpaceCastModel 𝓘(ℂ) x) v)))).2 =
    (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℂ) y) q
      (TotalSpace.mk' ℂ x v)).2 := by
  let cx := chartAt ℂ x
  let cq := chartAt ℂ q
  let F : ℂ → ℂ := cq ∘ cx.symm
  have h := StructureGroupoid.compatible (contDiffGroupoid ∞ 𝓘(ℂ))
    (chart_mem_atlas ℂ x) (chart_mem_atlas ℂ q)
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at h
  have hc : ContDiffOn ℂ ∞ F (cx.symm ≫ₕ cq).source := by
    simpa only [contDiffPregroupoid, mfld_simps] using h.1
  have hz : cx x ∈ (cx.symm ≫ₕ cq).source := by
    exact ⟨cx.map_source (mem_chart_source ℂ x), by simpa [cx, cq] using hx⟩
  have hd : DifferentiableAt ℂ F (cx x) :=
    (hc.differentiableOn (by simp)).differentiableAt
      ((cx.symm ≫ₕ cq).open_source.mem_nhds hz)
  have heq := hd.fderiv_restrictScalars (𝕜 := ℝ)
  simp only [TangentBundle.trivializationAt_apply, extChartAt, OpenPartialHomeomorph.extend,
    mfld_simps, fderivWithin_univ]
  change fderiv ℝ F (cx x) ((tangentSpaceCastModel 𝓘(ℂ) x) v) =
    fderiv ℂ F (cx x) v
  rw [heq]
  rfl


private theorem actual_same_atlas_real_tangent_field_has_continuous_complex_representative
    (V : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (hV : Continuous (fun x => TotalSpace.mk' ℂ x (V x))) :
    let W : ∀ x : E, TangentSpace 𝓘(ℂ) x := fun x =>
      (tangentSpaceCastModel 𝓘(ℂ) x).symm ((tangentSpaceCastModel 𝓘(ℝ,ℂ) x) (V x));
    Continuous (fun x => TotalSpace.mk' ℂ x (W x)) ∧
    (∀ x, W x = 0 ↔ V x = 0) ∧
    ∀ q x (hx : x ∈ (chartAt ℂ q).source),
      (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℂ) y) q
        (TotalSpace.mk' ℂ x (W x))).2 =
      (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q
        (TotalSpace.mk' ℂ x (V x))).2 := by
  dsimp only
  let W : ∀ x : E, TangentSpace 𝓘(ℂ) x := fun x =>
    (tangentSpaceCastModel 𝓘(ℂ) x).symm ((tangentSpaceCastModel 𝓘(ℝ,ℂ) x) (V x))
  have hcoord (q x : E) (hx : x ∈ (chartAt ℂ q).source) :
      (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℂ) y) q
        (TotalSpace.mk' ℂ x (W x))).2 =
      (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q
        (TotalSpace.mk' ℂ x (V x))).2 := by
    have hh := actual_same_atlas_real_complex_tangent_coordinates q x hx (W x)
    simpa only [W,ContinuousLinearEquiv.apply_symm_apply,ContinuousLinearEquiv.symm_apply_apply] using hh.symm
  refine ⟨?_,?_,hcoord⟩
  · apply continuous_iff_continuousAt.mpr
    intro q
    apply (FiberBundle.continuousAt_section ℂ q).mpr
    have hc := (FiberBundle.continuousAt_section ℂ q).mp (hV.continuousAt (x := q))
    apply hc.congr_of_eventuallyEq
    filter_upwards [(chartAt ℂ q).open_source.mem_nhds (mem_chart_source ℂ q)] with x hx
    exact hcoord q x hx
  · intro x
    simp only [W,ContinuousLinearEquiv.map_eq_zero_iff]
end
