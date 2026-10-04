import CurveComplexGenusTwo.Topology.ActualCanonicalZeroOrder.ActualTwoDirectionCoreStability
import CurveComplexGenusTwo.Topology.ActualSmoothMorseNormalForm.ActualLocalTangentPerturbation
import CurveComplexGenusTwo.Topology.ActualCanonicalZeroOrder.ActualTangentChartCoefficientOn
import Mathlib.Analysis.Calculus.FDeriv.Congr

open scoped Manifold ContDiff Bundle Topology
open Bundle Set Filter

theorem actual_tangent_prior_core_stability
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [T2Space E] [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (q p : E) (bump : SmoothBumpFunction 𝓘(ℝ,ℂ) p)
    (W : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (hW : ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (W x)))
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ (chartAt ℂ q).target)
    (hreg : ∀ z ∈ K,
      (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q
        (TotalSpace.mk' ℂ ((chartAt ℂ q).symm z) (W ((chartAt ℂ q).symm z)))).2 = 0 →
      (fderiv ℝ
        (fun w : ℂ =>
          (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q
            (TotalSpace.mk' ℂ ((chartAt ℂ q).symm w) (W ((chartAt ℂ q).symm w)))).2)
        z).det ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ c : ℂ, ‖c‖ < r →
      ∀ z ∈ K,
        (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q
          (TotalSpace.mk' ℂ ((chartAt ℂ q).symm z)
            (W ((chartAt ℂ q).symm z) +
              bump ((chartAt ℂ q).symm z) •
                (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) p).symmL ℝ
                  ((chartAt ℂ q).symm z) c))).2 = 0 →
        (fderiv ℝ
          (fun w : ℂ =>
            let x := (chartAt ℂ q).symm w
            (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q
              (TotalSpace.mk' ℂ x
                (W x + bump x •
                  (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) p).symmL ℝ x c))).2)
          z).det ≠ 0 := by
  let chart := chartAt ℂ q
  let eq := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q
  let ep := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) p
  let S1 : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x :=
    fun x => bump x • ep.symmL ℝ x 1
  let SI : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x :=
    fun x => bump x • ep.symmL ℝ x Complex.I
  let f : ℂ → ℂ := fun z =>
    (eq (TotalSpace.mk' ℂ (chart.symm z) (W (chart.symm z)))).2
  let g : ℂ → ℂ := fun z =>
    (eq (TotalSpace.mk' ℂ (chart.symm z) (S1 (chart.symm z)))).2
  let h : ℂ → ℂ := fun z =>
    (eq (TotalSpace.mk' ℂ (chart.symm z) (SI (chart.symm z)))).2
  have hf : ContDiffOn ℝ 1 f chart.target :=
    actual_tangent_chart_coefficient_contDiffOn W hW q
  have hg : ContDiffOn ℝ 1 g chart.target :=
    actual_tangent_chart_coefficient_contDiffOn S1
      (actual_supported_tangent_frame_smooth p 1 bump) q
  have hh : ContDiffOn ℝ 1 h chart.target :=
    actual_tangent_chart_coefficient_contDiffOn SI
      (actual_supported_tangent_frame_smooth p Complex.I bump) q
  obtain ⟨r, hr, hstable⟩ :=
    actual_two_direction_compact_regular_small_shifts f g h chart.target
      chart.open_target hf hg hh K hK hKU hreg
  refine ⟨r, hr, ?_⟩
  intro c hc z hz hzero
  let v' : ℂ → ℂ := fun w =>
    let x := chart.symm w
    (eq (TotalSpace.mk' ℂ x (W x + bump x • ep.symmL ℝ x c))).2
  have hEq : ∀ w ∈ chart.target,
      v' w = f w + c.re • g w + c.im • h w := by
    intro w hw
    let x := chart.symm w
    have hx : x ∈ chart.source := chart.map_target hw
    have hxbase : x ∈ eq.baseSet := by simpa [eq] using hx
    have hc : c.re • (1 : ℂ) + c.im • Complex.I = c := by
      apply Complex.ext <;> simp
    have hframe : bump x • ep.symmL ℝ x c =
        c.re • S1 x + c.im • SI x := by
      calc
        _ = bump x • ep.symmL ℝ x (c.re • (1 : ℂ) + c.im • Complex.I) := by rw [hc]
        _ = c.re • S1 x + c.im • SI x := by
          rw [map_add, map_smul, map_smul, smul_add]
          simp only [S1, SI, smul_smul]
          rw [mul_comm (bump x) c.re, mul_comm (bump x) c.im]
    change (eq ⟨x, W x + bump x • ep.symmL ℝ x c⟩).2 =
      (eq ⟨x, W x⟩).2 + c.re • (eq ⟨x, S1 x⟩).2 +
        c.im • (eq ⟨x, SI x⟩).2
    rw [hframe]
    simp only [← eq.continuousLinearMapAt_apply_of_mem (R := ℝ) hxbase,
      map_add, map_smul]
    abel
  have hzero' : f z + c.re • g z + c.im • h z = 0 := by
    rw [← hEq z (hKU hz)]
    exact hzero
  have hderiv : fderiv ℝ v' z =
      fderiv ℝ (fun w => f w + c.re • g w + c.im • h w) z := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [chart.open_target.mem_nhds (hKU hz)] with w hw
    exact hEq w hw
  simpa only [v'] using (hderiv ▸ hstable c hc z hz hzero')

#print axioms actual_tangent_prior_core_stability
