import CurveComplexGenusTwo.Topology.ActualLocalAnalyticSheaves.LocalSheafScaffold
import CurveComplexGenusTwo.Topology.ActualLocalAnalyticSheaves.ActualCanonicalLocalResidue

open scoped Manifold ContDiff Bundle
open Bundle
open Filter Topology Metric

namespace CanonicalDimensionTwo

theorem actualLocalOneForm_chart_center_eq_evaluation
    {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (p : E) :
    actualLocalOneForm s p ((chartAt ℂ p) p)
      (fun _ : Fin 1 => (1 : ℂ)) =
      actualCanonicalEvaluation p s := by
  rw [actualLocalOneForm_eq_global_in_chart s p p 1 (mem_chart_source ℂ p)]
  change s p
    ((trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℂ) y) p).symmL ℂ p 1) =
    s p ((tangentSpaceCastModel 𝓘(ℂ) p).symm 1)
  congr 1
  rw [TangentBundle.symmL_trivializationAt_eq_core (mem_chart_source ℂ p)]
  exact (tangentBundleCore 𝓘(ℂ) E).coordChange_self
    (achart ℂ p) p (mem_achart_source ℂ p) 1

theorem actualChartPole_residue_formula
    {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (p : E) (c : ℂ) (R : ℝ)
    (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt ℂ p) p) R ⊆
      (chartAt ℂ p).target) :
    (∮ z in C((chartAt ℂ p) p, R),
      (c / (z - (chartAt ℂ p) p)) *
        actualLocalOneForm s p z (fun _ : Fin 1 => (1 : ℂ))) =
      c * (2 * Real.pi * Complex.I) * actualCanonicalEvaluation p s := by
  let z₀ := (chartAt ℂ p) p
  have hc := actualLocalOneForm_circleIntegral_cauchy s p z₀ R hR htarget
  calc
    (∮ z in C(z₀, R), (c / (z - z₀)) *
      actualLocalOneForm s p z (fun _ : Fin 1 => (1 : ℂ))) =
      c * (∮ z in C(z₀, R), (z - z₀)⁻¹ *
        actualLocalOneForm s p z (fun _ : Fin 1 => (1 : ℂ))) := by
          simp only [div_eq_mul_inv, mul_assoc, circleIntegral.integral_const_mul]
    _ = c * (2 * Real.pi * Complex.I) * actualCanonicalEvaluation p s := by
      rw [actualLocalOneForm_chart_center_eq_evaluation] at hc
      simpa only [smul_eq_mul, mul_assoc] using congrArg (fun x : ℂ => c * x) hc

private theorem chartCircle_point_mem_overlap
    {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (p : E) (z : ℂ)
    (hz : z ∈ (chartAt ℂ p).target)
    (hne : z ≠ (chartAt ℂ p) p) :
    (chartAt ℂ p).symm z ∈
      SameAtlasRRLocal.overlapOpen p (SameAtlasRRLocal.chartSourceOpen p) := by
  have hsrc := (chartAt ℂ p).map_target hz
  have hpoint : (chartAt ℂ p).symm z ≠ p := by
    intro h
    apply hne
    simpa [h] using ((chartAt ℂ p).right_inv hz).symm
  exact ⟨hsrc, hpoint⟩

noncomputable def actualChartOverlapValue
    {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (p : E)
    (g : SameAtlasRRLocal.HolOn
      (SameAtlasRRLocal.overlapOpen p (SameAtlasRRLocal.chartSourceOpen p)))
    (z : ℂ) : ℂ := by
  classical
  exact if h : z ∈ (chartAt ℂ p).target ∧ z ≠ (chartAt ℂ p) p then
    g.1 ⟨(chartAt ℂ p).symm z,
      chartCircle_point_mem_overlap p z h.1 h.2⟩
  else 0

theorem actualChartOverlapValue_of_target_ne
    {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (p : E)
    (g : SameAtlasRRLocal.HolOn
      (SameAtlasRRLocal.overlapOpen p (SameAtlasRRLocal.chartSourceOpen p)))
    (z : ℂ) (hz : z ∈ (chartAt ℂ p).target)
    (hne : z ≠ (chartAt ℂ p) p) :
    actualChartOverlapValue p g z =
      g.1 ⟨(chartAt ℂ p).symm z,
        chartCircle_point_mem_overlap p z hz hne⟩ := by
  classical
  simp [actualChartOverlapValue, hz, hne]

noncomputable def actualChartPoleOverlapRepresentative
    {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (p : E) (c : ℂ) :
    SameAtlasRRLocal.HolOn
      (SameAtlasRRLocal.overlapOpen p (SameAtlasRRLocal.chartSourceOpen p)) :=
  SameAtlasRRLocal.poleToHolAway p _
    (by simp [SameAtlasRRLocal.overlapOpen, SameAtlasRRLocal.puncturedOpen])
    (SameAtlasRRLocal.PoleOneOn.restrict p
      (show SameAtlasRRLocal.overlapOpen p (SameAtlasRRLocal.chartSourceOpen p) ≤
        SameAtlasRRLocal.chartSourceOpen p by
        simp [SameAtlasRRLocal.overlapOpen])
      (SameAtlasRRLocal.chartPoleSection p c))

theorem actualChartPoleOverlapRepresentative_apply
    {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (p : E) (c z : ℂ)
    (hz : z ∈ (chartAt ℂ p).target)
    (hne : z ≠ (chartAt ℂ p) p) :
    actualChartOverlapValue p (actualChartPoleOverlapRepresentative p c) z =
      c / (z - (chartAt ℂ p) p) := by
  rw [actualChartOverlapValue_of_target_ne p _ z hz hne]
  simp [actualChartPoleOverlapRepresentative, SameAtlasRRLocal.poleToHolAway,
    SameAtlasRRLocal.PoleOneOn.restrict, SameAtlasRRLocal.chartPoleSection,
    (chartAt ℂ p).right_inv hz]

theorem actualChartPoleOverlapRepresentative_circleIntegral
    {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (p : E) (c : ℂ) (R : ℝ)
    (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt ℂ p) p) R ⊆
      (chartAt ℂ p).target) :
    (∮ z in C((chartAt ℂ p) p, R),
      actualChartOverlapValue p (actualChartPoleOverlapRepresentative p c) z *
        actualLocalOneForm s p z (fun _ : Fin 1 => (1 : ℂ))) =
      c * (2 * Real.pi * Complex.I) * actualCanonicalEvaluation p s := by
  rw [circleIntegral.integral_congr hR.le (fun z hz => ?_)]
  · exact actualChartPole_residue_formula s p c R hR htarget
  · have hzball : z ∈ Metric.closedBall ((chartAt ℂ p) p) R :=
      Metric.sphere_subset_closedBall hz
    have hzt := htarget hzball
    have hne : z ≠ (chartAt ℂ p) p := by
      intro he
      have hrzero : R = 0 := by simpa [he] using hz.symm
      exact hR.ne' hrzero
    rw [actualChartPoleOverlapRepresentative_apply p c z hzt hne]

theorem scalarCechBoundary_eq_overlap_representative
    {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (p : E) (c : ℂ) :
    SameAtlasRRLocal.scalarCechBoundary p c =
      (SameAtlasRRLocal.twoOpenCoboundary p
        (SameAtlasRRLocal.chartSourceOpen p)).range.mkQ
        (actualChartPoleOverlapRepresentative p c) := by
  rfl

noncomputable def actualChartHolValue
    {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (p : E) (h : SameAtlasRRLocal.HolOn (SameAtlasRRLocal.chartSourceOpen p))
    (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ (chartAt ℂ p).target then
    h.1 ⟨(chartAt ℂ p).symm z, (chartAt ℂ p).map_target hz⟩
  else 0

theorem actualChartHolValue_analyticAt_center
    {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (p : E) (h : SameAtlasRRLocal.HolOn (SameAtlasRRLocal.chartSourceOpen p)) :
    AnalyticAt ℂ (actualChartHolValue p h) ((chartAt ℂ p) p) := by
  classical
  obtain ⟨a, ha, he⟩ := h.property ⟨p, mem_chart_source ℂ p⟩
  have hz₀ : (chartAt ℂ p) p ∈ (chartAt ℂ p).target :=
    (chartAt ℂ p).map_source (mem_chart_source ℂ p)
  have htend : Tendsto (chartAt ℂ p).symm (𝓝 ((chartAt ℂ p) p)) (𝓝 p) := by
    have hc := (chartAt ℂ p).symm.continuousOn.continuousAt
      ((chartAt ℂ p).open_target.mem_nhds hz₀)
    simpa [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)] using hc.tendsto
  apply ha.congr
  filter_upwards [((chartAt ℂ p).open_target.mem_nhds hz₀),
    htend.eventually he] with z hz hlocal
  simpa [actualChartHolValue, hz, (chartAt ℂ p).right_inv hz] using
    (hlocal ((chartAt ℂ p).map_target hz)).symm

theorem actualChartTransition_analytic
    {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (p x : E) (hx : x ∈ (chartAt ℂ p).source) :
    AnalyticAt ℂ (fun z : ℂ => (chartAt ℂ x) ((chartAt ℂ p).symm z))
      ((chartAt ℂ p) x) := by
  let z := (chartAt ℂ p) x
  have hz : z ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source hx
  have hsymm : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ (chartAt ℂ p).symm z :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hz
  have hchart : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ (chartAt ℂ x) x :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x)
      (mem_chart_source ℂ x)
  have hchart' : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ (chartAt ℂ x)
      ((chartAt ℂ p).symm z) := by
    simpa [z, (chartAt ℂ p).left_inv hx] using hchart
  have hcomp : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞
      ((chartAt ℂ x) ∘ (chartAt ℂ p).symm) z := hchart'.comp z hsymm
  have hsmooth : ContDiffAt ℂ ∞
      ((chartAt ℂ x) ∘ (chartAt ℂ p).symm) z := hcomp.contDiffAt
  obtain ⟨t, ht, hdiff⟩ := hsmooth.contDiffOn (m := 1) (by simp) (by simp)
  exact (hdiff.differentiableOn (by norm_num)).analyticAt ht

theorem actualChartHolValue_analyticAt_of_mem_target
    {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (p : E) (h : SameAtlasRRLocal.HolOn (SameAtlasRRLocal.chartSourceOpen p))
    (z : ℂ) (hz : z ∈ (chartAt ℂ p).target) :
    AnalyticAt ℂ (actualChartHolValue p h) z := by
  classical
  let x := (chartAt ℂ p).symm z
  have hx : x ∈ (chartAt ℂ p).source := (chartAt ℂ p).map_target hz
  obtain ⟨a, ha, he⟩ := h.property ⟨x, hx⟩
  let b : ℂ → ℂ := fun w => (chartAt ℂ x) ((chartAt ℂ p).symm w)
  have hb : AnalyticAt ℂ b z := by
    simpa [b, x, (chartAt ℂ p).right_inv hz] using
      actualChartTransition_analytic p x hx
  have hbval : b z = (chartAt ℂ x) x := rfl
  have hab : AnalyticAt ℂ (fun w => a (b w)) z := by
    exact ha.comp_of_eq hb hbval
  have htend : Tendsto (chartAt ℂ p).symm (𝓝 z) (𝓝 x) := by
    exact (chartAt ℂ p).symm.continuousOn.continuousAt
      ((chartAt ℂ p).open_target.mem_nhds hz) |>.tendsto
  apply hab.congr
  filter_upwards [((chartAt ℂ p).open_target.mem_nhds hz),
    htend.eventually he] with w hw hlocal
  simpa [actualChartHolValue, hw, b] using
    (hlocal ((chartAt ℂ p).map_target hw)).symm

theorem actualChartHolValue_times_section_small_circle_zero
    {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (p : E) (h : SameAtlasRRLocal.HolOn (SameAtlasRRLocal.chartSourceOpen p))
    (s : ActualCanonicalSection E) :
    ∃ R : ℝ, 0 < R ∧
      Metric.closedBall ((chartAt ℂ p) p) R ⊆ (chartAt ℂ p).target ∧
      (∮ z in C((chartAt ℂ p) p, R),
        actualChartHolValue p h z *
          actualLocalOneForm s p z (fun _ : Fin 1 => (1 : ℂ))) = 0 := by
  let z₀ := (chartAt ℂ p) p
  let f : ℂ → ℂ := fun z => actualChartHolValue p h z *
    actualLocalOneForm s p z (fun _ : Fin 1 => (1 : ℂ))
  have ha : AnalyticAt ℂ f z₀ :=
    (actualChartHolValue_analyticAt_center p h).mul
      (actualLocalOneForm_coefficient_analytic s p)
  have hd : {z : ℂ | DifferentiableAt ℂ f z} ∈ 𝓝 z₀ :=
    ha.eventually_analyticAt.mono (fun z hz => hz.differentiableAt)
  have htarget : (chartAt ℂ p).target ∈ 𝓝 z₀ :=
    (chartAt ℂ p).open_target.mem_nhds
      ((chartAt ℂ p).map_source (mem_chart_source ℂ p))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hd htarget)
  refine ⟨ε / 2, half_pos hε, ?_, ?_⟩
  · intro z hz
    exact (hball (Metric.closedBall_subset_ball (half_lt_self hε) hz)).2
  · have hdiff : DifferentiableOn ℂ f (Metric.closedBall z₀ (ε / 2)) := by
      intro z hz
      exact DifferentiableAt.differentiableWithinAt (show DifferentiableAt ℂ f z from
        (hball (Metric.closedBall_subset_ball (half_lt_self hε) hz)).1)
    exact (hdiff.mono closure_ball_subset_closedBall).diffContOnCl
      |>.circleIntegral_eq_zero (half_pos hε).le

theorem actualChartHolRestrict_small_circle_zero
    {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (p : E) (h : SameAtlasRRLocal.HolOn (SameAtlasRRLocal.chartSourceOpen p))
    (s : ActualCanonicalSection E) :
    ∃ R : ℝ, 0 < R ∧
      Metric.closedBall ((chartAt ℂ p) p) R ⊆ (chartAt ℂ p).target ∧
      (∮ z in C((chartAt ℂ p) p, R),
        actualChartOverlapValue p
          (SameAtlasRRLocal.HolOn.restrict
            (show SameAtlasRRLocal.overlapOpen p
              (SameAtlasRRLocal.chartSourceOpen p) ≤
              SameAtlasRRLocal.chartSourceOpen p by
              simp [SameAtlasRRLocal.overlapOpen]) h) z *
          actualLocalOneForm s p z (fun _ : Fin 1 => (1 : ℂ))) = 0 := by
  obtain ⟨R, hR, htarget, hzero⟩ :=
    actualChartHolValue_times_section_small_circle_zero p h s
  refine ⟨R, hR, htarget, ?_⟩
  rw [circleIntegral.integral_congr hR.le (fun z hz => ?_)]
  · exact hzero
  · have hzt : z ∈ (chartAt ℂ p).target :=
      htarget (Metric.sphere_subset_closedBall hz)
    have hne : z ≠ (chartAt ℂ p) p := by
      intro he
      have hrzero : R = 0 := by simpa [he] using hz.symm
      exact hR.ne' hrzero
    rw [actualChartOverlapValue_of_target_ne p _ z hzt hne]
    simp [actualChartHolValue, hzt, SameAtlasRRLocal.HolOn.restrict]

theorem actualChartHolValue_times_section_circle_zero
    {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (p : E) (h : SameAtlasRRLocal.HolOn (SameAtlasRRLocal.chartSourceOpen p))
    (s : ActualCanonicalSection E) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt ℂ p) p) R ⊆
      (chartAt ℂ p).target) :
    (∮ z in C((chartAt ℂ p) p, R),
      actualChartHolValue p h z *
        actualLocalOneForm s p z (fun _ : Fin 1 => (1 : ℂ))) = 0 := by
  let f : ℂ → ℂ := fun z => actualChartHolValue p h z *
    actualLocalOneForm s p z (fun _ : Fin 1 => (1 : ℂ))
  have hd : DifferentiableOn ℂ f (Metric.closedBall ((chartAt ℂ p) p) R) := by
    intro z hz
    have hzt := htarget hz
    have hsrc := (chartAt ℂ p).map_target hzt
    have hs : AnalyticAt ℂ
        (fun w => actualLocalOneForm s p w (fun _ : Fin 1 => (1 : ℂ))) z := by
      simpa [(chartAt ℂ p).right_inv hzt] using
        actualLocalOneForm_coefficient_analytic_on_chart s p
          ((chartAt ℂ p).symm z) hsrc
    have ha := (actualChartHolValue_analyticAt_of_mem_target p h z hzt).mul hs
    exact ha.differentiableAt.differentiableWithinAt
  exact (hd.mono closure_ball_subset_closedBall).diffContOnCl
    |>.circleIntegral_eq_zero hR.le

theorem actualChartHolRestrict_circle_zero
    {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (p : E) (h : SameAtlasRRLocal.HolOn (SameAtlasRRLocal.chartSourceOpen p))
    (s : ActualCanonicalSection E) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt ℂ p) p) R ⊆
      (chartAt ℂ p).target) :
    (∮ z in C((chartAt ℂ p) p, R),
      actualChartOverlapValue p
        (SameAtlasRRLocal.HolOn.restrict
          (show SameAtlasRRLocal.overlapOpen p
            (SameAtlasRRLocal.chartSourceOpen p) ≤
            SameAtlasRRLocal.chartSourceOpen p by
            simp [SameAtlasRRLocal.overlapOpen]) h) z *
        actualLocalOneForm s p z (fun _ : Fin 1 => (1 : ℂ))) = 0 := by
  rw [circleIntegral.integral_congr hR.le (fun z hz => ?_)]
  · exact actualChartHolValue_times_section_circle_zero p h s R hR htarget
  · have hzt : z ∈ (chartAt ℂ p).target :=
      htarget (Metric.sphere_subset_closedBall hz)
    have hne : z ≠ (chartAt ℂ p) p := by
      intro he
      have hrzero : R = 0 := by simpa [he] using hz.symm
      exact hR.ne' hrzero
    rw [actualChartOverlapValue_of_target_ne p _ z hzt hne]
    simp [actualChartHolValue, hzt, SameAtlasRRLocal.HolOn.restrict]

end CanonicalDimensionTwo
