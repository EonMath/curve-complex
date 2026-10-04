import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualMorseGlobalGradientField
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

open scoped Manifold ContDiff Bundle
open Bundle Set Filter Topology

theorem actual_chart_tangent_scalar_derivative_identity
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (p x : E) (hx : x ∈ (chartAt ℂ p).source)
    (F : E → ℝ) (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F)
    (v : ℂ) :
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F x))
      ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x)
        ((trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) p).symmL ℝ x v)) =
      (fderiv ℝ (fun z : ℂ => F ((chartAt ℂ p).symm z)) ((chartAt ℂ p) x)) v := by
  let c := chartAt ℂ p
  let e := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) p
  let f : ℂ → ℝ := fun z => F (c.symm z)
  have hcDiff : MDifferentiableAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) c x :=
    mdifferentiableAt_atlas (I := 𝓘(ℝ,ℂ)) (ChartedSpace.chart_mem_atlas _) hx
  have hfDiff : MDifferentiableAt 𝓘(ℝ,ℂ) 𝓘(ℝ) f (c x) := by
    have hsmooth := actual_smooth_scalar_chart_pullback_contDiffOn_infty p F hF
    exact (((hsmooth (c x) (c.map_source hx)).contDiffAt
      (c.open_target.mem_nhds (c.map_source hx))).contMDiffAt).mdifferentiableAt
        (by simp)
  have hcomp := mfderiv_comp_apply x hfDiff hcDiff (e.symmL ℝ x v)
  have hfun : (f ∘ c) =ᶠ[𝓝 x] F := by
    filter_upwards [c.open_source.mem_nhds hx] with y hy
    simp [f, c.left_inv hy]
  have hFderiv := Filter.EventuallyEq.mfderiv_eq
    (I := 𝓘(ℝ,ℂ)) (I' := 𝓘(ℝ)) hfun
  rw [hFderiv] at hcomp
  have hchart : (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) c x) (e.symmL ℝ x v) = v := by
    rw [mfderiv_chartAt_eq_tangentCoordChange hx]
    change ((tangentBundleCore 𝓘(ℝ,ℂ) E).coordChange
      (achart ℂ x) (achart ℂ p) x) (e.symmL ℝ x v) = v
    rw [← TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hx]
    exact e.continuousLinearMapAt_symmL (by simpa [e] using hx) v
  rw [hchart] at hcomp
  simp only [Function.comp_apply, f] at hcomp
  rw [c.left_inv hx] at hcomp
  change (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x) (e.symmL ℝ x v) =
    (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) f (c x)) v at hcomp
  rw [mfderiv_eq_fderiv] at hcomp
  have hval : f (c x) = F x := by simp [f, c.left_inv hx]
  rw [hval] at hcomp
  change (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x) (e.symmL ℝ x v) =
    (fderiv ℝ f (c x)) v at hcomp
  change (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x) (e.symmL ℝ x v) =
    (fderiv ℝ f (c x)) v
  exact hcomp

