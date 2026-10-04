import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.Complex.Basic

open scoped Manifold ContDiff Bundle Topology
open Bundle

theorem actual_real_tangent_transition_differentiable
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (q r : E) (hqr : q ∈ (chartAt ℂ r).source) :
    DifferentiableAt ℝ
      (fun w : ℂ =>
        ((trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) r).coordChangeL
          ℝ (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q)
          ((chartAt ℂ q).symm ((chartAt ℂ q) q + w)) : ℂ →L[ℝ] ℂ)) 0 := by
  let cq := chartAt ℂ q
  let eq := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q
  let er := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) r
  let A : E → ℂ →L[ℝ] ℂ := fun x => er.coordChangeL ℝ eq x
  have hqeq : q ∈ eq.baseSet := mem_baseSet_trivializationAt ℂ _ q
  have hqer : q ∈ er.baseSet := by simpa [er] using hqr
  have hA : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ →L[ℝ] ℂ) ∞ A q :=
    contMDiffAt_coordChangeL hqer hqeq
  have hqt : cq q ∈ cq.target := cq.map_source (mem_chart_source ℂ q)
  have hsymm : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ cq.symm (cq q) :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ,ℂ)) (x := q) (n := ∞)
      (cq q) hqt).contMDiffAt (cq.open_target.mem_nhds hqt)
  have hcomp : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ →L[ℝ] ℂ) ∞
      (fun z : ℂ => A (cq.symm z)) (cq q) := by
    have hq : cq.symm (cq q) = q := cq.left_inv (mem_chart_source ℂ q)
    have hA' : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ →L[ℝ] ℂ) ∞ A (cq.symm (cq q)) := by
      simpa only [hq] using hA
    simpa only [Function.comp_def] using hA'.comp (cq q) hsymm
  have hraw : ContDiffAt ℝ ∞ (fun z : ℂ => A (cq.symm z)) (cq q) := by
    have hc := (contMDiffAt_iff_of_mem_source
      (I := 𝓘(ℝ,ℂ)) (I' := 𝓘(ℝ,ℂ →L[ℝ] ℂ)) (n := ∞)
      (mem_chart_source ℂ (cq q)) (mem_chart_source (ℂ →L[ℝ] ℂ) (A (cq.symm (cq q))))).mp hcomp
    simpa only [Function.comp_def, contDiffWithinAt_univ, mfld_simps,
      extChartAt, OpenPartialHomeomorph.extend, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id] using hc.2
  have hshift : ContDiffAt ℝ ∞ (fun w : ℂ => cq q + w) 0 :=
    contDiffAt_const.add contDiffAt_id
  have hraw' : ContDiffAt ℝ ∞ (fun z : ℂ => A (cq.symm z)) (cq q + (0 : ℂ)) :=
    by simpa using hraw
  have hresult : ContDiffAt ℝ ∞ (fun w : ℂ => A (cq.symm (cq q + w))) 0 := by
    simpa only [Function.comp_def] using hraw'.comp 0 hshift
  exact hresult.differentiableAt (by norm_num)

