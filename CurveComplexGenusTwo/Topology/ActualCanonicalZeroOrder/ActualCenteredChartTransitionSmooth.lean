import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.Complex.Basic

open scoped Manifold ContDiff Topology

theorem actual_centered_chart_transition_contDiffAt
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (x q r : E) (hxq : x ∈ (chartAt ℂ q).source)
    (hxr : x ∈ (chartAt ℂ r).source) :
    ContDiffAt ℝ 1
      (fun w : ℂ =>
        (chartAt ℂ r) ((chartAt ℂ q).symm ((chartAt ℂ q) x + w)) -
          (chartAt ℂ r) x) 0 := by
  let cq := chartAt ℂ q
  let cr := chartAt ℂ r
  have hqtarget : cq x ∈ cq.target := cq.map_source hxq
  have hsymm : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ cq.symm (cq x) :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ,ℂ)) (x := q) (n := ∞)
      (cq x) hqtarget).contMDiffAt
      (cq.open_target.mem_nhds hqtarget)
  have hchart : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ cr x :=
    (contMDiffOn_chart (I := 𝓘(ℝ,ℂ)) (x := r) (n := ∞) x hxr).contMDiffAt
      (cr.open_source.mem_nhds hxr)
  have hcomp : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞
      (fun z : ℂ => cr (cq.symm z)) (cq x) := by
    have hq : cq.symm (cq x) = x := cq.left_inv hxq
    have hchart' : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ cr (cq.symm (cq x)) := by
      simpa only [hq] using hchart
    have hc := hchart'.comp (cq x) hsymm
    simpa only [Function.comp_def] using hc
  have hraw : ContDiffAt ℝ ∞ (fun z : ℂ => cr (cq.symm z)) (cq x) := by
    have hc := (contMDiffAt_iff_of_mem_source
      (I := 𝓘(ℝ,ℂ)) (I' := 𝓘(ℝ,ℂ)) (n := ∞)
      (mem_chart_source ℂ (cq x)) (mem_chart_source ℂ (cr (cq.symm (cq x))))).mp hcomp
    simpa only [Function.comp_def, contDiffWithinAt_univ, mfld_simps,
      extChartAt, OpenPartialHomeomorph.extend, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id] using hc.2
  have hshift : ContDiffAt ℝ ∞ (fun w : ℂ => cq x + w) 0 :=
    contDiffAt_const.add contDiffAt_id
  have hraw' : ContDiffAt ℝ ∞ (fun z : ℂ => cr (cq.symm z)) (cq x + (0 : ℂ)) :=
    by simpa using hraw
  have htrans := hraw'.comp 0 hshift
  have hsub := htrans.sub (contDiffAt_const (c := cr x))
  simpa only [cq, cr, Function.comp_def] using
    hsub.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)

#print axioms actual_centered_chart_transition_contDiffAt
