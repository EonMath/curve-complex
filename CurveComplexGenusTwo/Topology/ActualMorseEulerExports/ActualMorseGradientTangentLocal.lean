import CurveComplexGenusTwo.Topology.ActualSmoothMorseNormalForm.ActualMorseChartPullbackSmooth
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

open scoped Manifold ContDiff Bundle
open Bundle Set

theorem actual_chart_gradient_tangent_section_smooth_on_source
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (p : E) (F : E → ℝ)
    (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F) :
    let c := chartAt ℂ p;
    let e := trivializationAt ℂ (fun x : E => TangentSpace 𝓘(ℝ,ℂ) x) p;
    ContMDiffOn 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x
        (e.symmL ℝ x (gradient (fun z => F (c.symm z)) (c x)))) c.source := by
  let c := chartAt ℂ p
  let e := trivializationAt ℂ (fun x : E => TangentSpace 𝓘(ℝ,ℂ) x) p
  have hc : ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ (fun x => c x) c.source := by
    have h := contMDiffOn_extChartAt (I := 𝓘(ℝ,ℂ)) (x := p) (n := ∞)
    apply h.congr
    intro x hx
    simp [c, extChartAt, OpenPartialHomeomorph.extend]
  have hg : ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞
      (gradient (fun z => F (c.symm z))) c.target :=
    (actual_smooth_scalar_chart_gradient_contDiffOn_infty p F hF).contMDiffOn
  have hgc : ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞
      (fun x => gradient (fun z => F (c.symm z)) (c x)) c.source := by
    exact hg.comp hc (fun x hx => c.map_source hx)
  have hbase : e.baseSet = c.source := by
    simp [e, c, TangentBundle.trivializationAt_baseSet]
  dsimp only
  rw [← hbase]
  rw [e.contMDiffOn_section_baseSet_iff]
  apply hgc.congr
  intro x hx
  change (e ⟨x, e.symmL ℝ x (gradient (fun z => F (c.symm z)) (c x))⟩).2 =
    gradient (fun z => F (c.symm z)) (c x)
  rw [e.symmL_apply hx]
  rw [e.mk_symm hx]
  exact congrArg Prod.snd (e.apply_symm_apply (show (x, _) ∈ e.target from by simpa [e] using hx))


theorem actual_supported_chart_gradient_tangent_smooth
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (p : E) (F : E → ℝ)
    (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F)
    (b : E → ℝ) (hb : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ b)
    (hs : tsupport b ⊆ (chartAt ℂ p).source) :
    let c := chartAt ℂ p;
    let e := trivializationAt ℂ (fun x : E => TangentSpace 𝓘(ℝ,ℂ) x) p;
    ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x
        (b x • e.symmL ℝ x (gradient (fun z => F (c.symm z)) (c x)))) := by
  let c := chartAt ℂ p
  let e := trivializationAt ℂ (fun x : E => TangentSpace 𝓘(ℝ,ℂ) x) p
  apply ContMDiffOn.smul_section_of_tsupport
    (u := e.baseSet)
    (s := fun x => e.symmL ℝ x (gradient (fun z => F (c.symm z)) (c x)))
  · exact hb.contMDiffOn
  · exact e.open_baseSet
  · simpa only [e, TangentBundle.trivializationAt_baseSet] using hs
  · simpa only [e, c, TangentBundle.trivializationAt_baseSet] using
      actual_chart_gradient_tangent_section_smooth_on_source p F hF

