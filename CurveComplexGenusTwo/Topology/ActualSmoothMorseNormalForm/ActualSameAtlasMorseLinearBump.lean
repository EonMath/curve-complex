import CurveComplexGenusTwo.Topology.ActualSmoothMorseNormalForm.ActualSameAtlasMorsePlateau
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Analysis.Complex.Basic

open scoped Manifold ContDiff Topology
open Set

theorem actual_chart_linear_bump_smooth
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (p : E) (b : E → ℝ) (L : ℂ →L[ℝ] ℝ)
    (hb : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ b)
    (hs : tsupport b ⊆ (chartAt ℂ p).source) :
    ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞
      (fun x => b x * L ((chartAt ℂ p) x)) := by
  apply contMDiff_of_tsupport
  intro x hx
  have hxb : x ∈ tsupport b := by
    exact tsupport_smul_subset_left b
      (fun y => L ((chartAt ℂ p) y)) (by simpa only [smul_eq_mul] using hx)
  have hxs : x ∈ (chartAt ℂ p).source := hs hxb
  have hchart : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞
      (fun y => (chartAt ℂ p) y) x := by
    apply (contMDiffAt_extChartAt' (I := 𝓘(ℝ,ℂ)) hxs).congr_of_eventuallyEq
    filter_upwards [(chartAt ℂ p).open_source.mem_nhds hxs] with y hy
    simp [extChartAt, OpenPartialHomeomorph.extend]
  have hre : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞
      (fun y => L ((chartAt ℂ p) y)) x := by
    exact (L.contMDiff.contMDiffAt).comp x hchart
  exact hb.contMDiffAt.mul hre

#print axioms actual_chart_linear_bump_smooth

theorem actual_chart_linear_bump_plateau
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    (p : E) (b : E → ℝ) (L : ℂ →L[ℝ] ℝ)
    (U : Set E) (hone : ∀ x ∈ U, b x = 1) :
    ∀ x ∈ U, b x * L ((chartAt ℂ p) x) = L ((chartAt ℂ p) x) := by
  intro x hx
  rw [hone x hx, one_mul]

#print axioms actual_chart_linear_bump_plateau

theorem actual_finite_chart_affine_scalar_family_smooth
    {E ι : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E] [Fintype ι]
    (F : E → ℝ) (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F)
    (p : ι → E) (b : ι → E → ℝ) (L : ι → ℂ →L[ℝ] ℝ)
    (hb : ∀ i, ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ (b i))
    (hs : ∀ i, tsupport (b i) ⊆ (chartAt ℂ (p i)).source)
    (a : ι → ℝ) :
    ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞
      (fun x => F x + ∑ i, a i * (b i x * L i ((chartAt ℂ (p i)) x))) := by
  apply hF.add
  apply ContMDiff.sum
  intro i hi
  exact contMDiff_const.mul (actual_chart_linear_bump_smooth (p i) (b i) (L i) (hb i) (hs i))

#print axioms actual_finite_chart_affine_scalar_family_smooth
