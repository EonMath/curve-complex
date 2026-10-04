import CurveComplexGenusTwo.Topology.ActualLocalDbarSolvability.ActualLocalDbarContracts
import CurveComplexGenusTwo.Topology.ActualLocalAnalyticSheaves.LocalSheafScaffold
import Mathlib.Analysis.Complex.Conformal

open scoped Manifold ContDiff Bundle Distributions
open Filter Topology
open CanonicalDimensionTwo.LocalDbar

namespace CanonicalDimensionTwo

theorem actualDbar_zero_iff_complex_differentiableAt
    {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    dbar f z = 0 ↔ DifferentiableAt ℂ f z := by
  rw [differentiableAt_complex_iff_differentiableAt_real]
  constructor
  · intro hz
    refine ⟨hf, ?_⟩
    have hz' : fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I = 0 := by
      simpa only [dbar, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false] using hz
    have he : Complex.I * fderiv ℝ f z 1 - fderiv ℝ f z Complex.I = 0 := by
      calc
        _ = Complex.I * (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I) := by
          rw [mul_add, ← mul_assoc, Complex.I_mul_I]
          ring
        _ = 0 := by rw [hz', mul_zero]
    exact (sub_eq_zero.mp he).symm
  · rintro ⟨_, he⟩
    simp only [smul_eq_mul] at he
    simp [dbar, he, ← mul_assoc, Complex.I_mul_I]

theorem actualSmooth_dbar_zero_iff_analyticOnNhd
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) :
    (∀ z ∈ U, dbar f z = 0) ↔ AnalyticOnNhd ℂ f U := by
  constructor
  · intro hz
    apply DifferentiableOn.analyticOnNhd _ hU
    intro z hzu
    exact ((actualDbar_zero_iff_complex_differentiableAt
      ((hf.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hzu))).mp
        (hz z hzu)).differentiableWithinAt
  · intro ha z hz
    exact (actualDbar_zero_iff_complex_differentiableAt
      ((hf.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hz))).mpr
        (ha z hz).differentiableAt

/-- The smooth zero-∂̄ condition supplies the literal chart-germ witnesses
required by the actual scalar holomorphic sheaf. -/
theorem actualHolOn_of_chart_smooth_dbar_zero
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ∞ E] (U : TopologicalSpace.Opens E) (f : E → ℂ)
    (hsmooth : ∀ x : U, ∃ V : Set ℂ, IsOpen V ∧
      (chartAt ℂ (x : E)) x ∈ V ∧
      ContDiffOn ℝ ∞ (fun z => f ((chartAt ℂ (x : E)).symm z)) V)
    (hzero : ∀ x : U, ∀ᶠ z in 𝓝 ((chartAt ℂ (x : E)) x),
      dbar (fun w => f ((chartAt ℂ (x : E)).symm w)) z = 0) :
    SameAtlasRRLocal.IsHolOn U (fun x => f x) := by
  intro x
  obtain ⟨V, hV, hxV, hdiff⟩ := hsmooth x
  obtain ⟨W, hW, hWopen, hxW⟩ := eventually_nhds_iff.mp (hzero x)
  have hVW : IsOpen (V ∩ W) := hV.inter hWopen
  have ha := (actualSmooth_dbar_zero_iff_analyticOnNhd hVW
    (hdiff.mono Set.inter_subset_left)).mp (fun z hz => hW z hz.2)
  refine ⟨fun z => f ((chartAt ℂ (x : E)).symm z), ha _ ⟨hxV, hxW⟩, ?_⟩
  filter_upwards [(chartAt ℂ (x : E)).open_source.mem_nhds (mem_chart_source ℂ (x : E))]
    with y hy hyU
  rw [(chartAt ℂ (x : E)).left_inv hy]

#print axioms actualHolOn_of_chart_smooth_dbar_zero
end CanonicalDimensionTwo
