import CurveComplexGenusTwo.Topology.ActualLocalAnalyticSheaves.ActualCechResidue

open scoped Manifold ContDiff Bundle
open Bundle Filter Topology Metric
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace CanonicalDimensionTwo

section Local
variable {E : Type} [TopologicalSpace E]
  [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]

noncomputable def actualChartOverlapEvaluation (p : E) (z : ℂ) :
    SameAtlasRRLocal.HolOn
      (SameAtlasRRLocal.overlapOpen p (SameAtlasRRLocal.chartSourceOpen p)) →ₗ[ℂ] ℂ where
  toFun g := actualChartOverlapValue p g z
  map_add' g h := by
    classical
    simp only [actualChartOverlapValue]
    split <;> simp
  map_smul' c g := by
    classical
    simp only [actualChartOverlapValue]
    split <;> simp

noncomputable def actualLocalOneFormCoefficient (p : E) (z : ℂ) :
    ActualCanonicalSection E →ₗ[ℂ] ℂ where
  toFun s := actualLocalOneForm s p z (fun _ : Fin 1 => (1 : ℂ))
  map_add' s t := by
    simp [actualLocalOneForm_apply, ContinuousLinearMap.inCoordinates]
  map_smul' c s := by
    simp [actualLocalOneForm_apply, ContinuousLinearMap.inCoordinates]

theorem actualChartOverlapValue_analyticAt
    (p : E)
    (g : SameAtlasRRLocal.HolOn
      (SameAtlasRRLocal.overlapOpen p (SameAtlasRRLocal.chartSourceOpen p)))
    (z : ℂ) (hz : z ∈ (chartAt ℂ p).target)
    (hne : z ≠ (chartAt ℂ p) p) :
    AnalyticAt ℂ (actualChartOverlapValue p g) z := by
  classical
  let x := (chartAt ℂ p).symm z
  have hx : x ∈ (chartAt ℂ p).source := (chartAt ℂ p).map_target hz
  have hxp : x ≠ p := by
    intro h
    exact hne ((chartAt ℂ p).right_inv hz |>.symm.trans (congrArg (chartAt ℂ p) h))
  obtain ⟨a, ha, he⟩ := g.property ⟨x, hx, hxp⟩
  let b : ℂ → ℂ := fun w => (chartAt ℂ x) ((chartAt ℂ p).symm w)
  have hb : AnalyticAt ℂ b z := by
    simpa [b, x, (chartAt ℂ p).right_inv hz] using
      actualChartTransition_analytic p x hx
  have hab : AnalyticAt ℂ (fun w => a (b w)) z := ha.comp_of_eq hb rfl
  have htend : Tendsto (chartAt ℂ p).symm (𝓝 z) (𝓝 x) := by
    exact (chartAt ℂ p).symm.continuousOn.continuousAt
      ((chartAt ℂ p).open_target.mem_nhds hz) |>.tendsto
  apply hab.congr
  filter_upwards [(chartAt ℂ p).open_target.mem_nhds hz,
    isOpen_compl_singleton.mem_nhds hne, htend.eventually he] with w hw hwp hlocal
  rw [actualChartOverlapValue_of_target_ne p g w hw hwp]
  exact (hlocal _).symm

theorem actualChartOverlap_times_section_analyticAt
    (p : E)
    (g : SameAtlasRRLocal.HolOn
      (SameAtlasRRLocal.overlapOpen p (SameAtlasRRLocal.chartSourceOpen p)))
    (s : ActualCanonicalSection E) (z : ℂ)
    (hz : z ∈ (chartAt ℂ p).target)
    (hne : z ≠ (chartAt ℂ p) p) :
    AnalyticAt ℂ (fun w => actualChartOverlapValue p g w *
      actualLocalOneForm s p w (fun _ : Fin 1 => (1 : ℂ))) z := by
  apply (actualChartOverlapValue_analyticAt p g z hz hne).mul
  simpa [(chartAt ℂ p).right_inv hz] using
    actualLocalOneForm_coefficient_analytic_on_chart s p
      ((chartAt ℂ p).symm z) ((chartAt ℂ p).map_target hz)

theorem actualChartOverlap_times_section_circleIntegrable
    (p : E)
    (g : SameAtlasRRLocal.HolOn
      (SameAtlasRRLocal.overlapOpen p (SameAtlasRRLocal.chartSourceOpen p)))
    (s : ActualCanonicalSection E) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt ℂ p) p) R ⊆ (chartAt ℂ p).target) :
    CircleIntegrable (fun z => actualChartOverlapValue p g z *
      actualLocalOneForm s p z (fun _ : Fin 1 => (1 : ℂ))) ((chartAt ℂ p) p) R := by
  apply ContinuousOn.circleIntegrable hR.le
  intro z hz
  apply (actualChartOverlap_times_section_analyticAt p g s z
    (htarget (Metric.sphere_subset_closedBall hz)) ?_).continuousAt.continuousWithinAt
  intro he
  have : R = 0 := by simpa [he] using hz.symm
  exact hR.ne' this

theorem actualChartOverlap_circleIntegral_radius_le
    (p : E)
    (g : SameAtlasRRLocal.HolOn
      (SameAtlasRRLocal.overlapOpen p (SameAtlasRRLocal.chartSourceOpen p)))
    (s : ActualCanonicalSection E) (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R)
    (htarget : Metric.closedBall ((chartAt ℂ p) p) R ⊆ (chartAt ℂ p).target) :
    (∮ z in C((chartAt ℂ p) p, R), actualChartOverlapValue p g z *
      actualLocalOneForm s p z (fun _ : Fin 1 => (1 : ℂ))) =
    (∮ z in C((chartAt ℂ p) p, r), actualChartOverlapValue p g z *
      actualLocalOneForm s p z (fun _ : Fin 1 => (1 : ℂ))) := by
  apply Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
    hr hrR (s := ∅) Set.countable_empty
  · intro z hz
    apply (actualChartOverlap_times_section_analyticAt p g s z (htarget hz.1)
      ?_).continuousAt.continuousWithinAt
    intro he
    exact hz.2 (by simpa [he] using hr)
  · intro z hz
    apply (actualChartOverlap_times_section_analyticAt p g s z
      (htarget (Metric.ball_subset_closedBall hz.1.1)) ?_).differentiableAt
    intro he
    exact hz.1.2 (by simp [he, hr.le])

theorem actualChartOverlap_circleIntegral_radius_independent
    (p : E)
    (g : SameAtlasRRLocal.HolOn
      (SameAtlasRRLocal.overlapOpen p (SameAtlasRRLocal.chartSourceOpen p)))
    (s : ActualCanonicalSection E) (r R : ℝ) (hr : 0 < r) (hR : 0 < R)
    (htarget_r : Metric.closedBall ((chartAt ℂ p) p) r ⊆ (chartAt ℂ p).target)
    (htarget_R : Metric.closedBall ((chartAt ℂ p) p) R ⊆ (chartAt ℂ p).target) :
    (∮ z in C((chartAt ℂ p) p, R), actualChartOverlapValue p g z *
      actualLocalOneForm s p z (fun _ : Fin 1 => (1 : ℂ))) =
    (∮ z in C((chartAt ℂ p) p, r), actualChartOverlapValue p g z *
      actualLocalOneForm s p z (fun _ : Fin 1 => (1 : ℂ))) := by
  rcases le_total r R with h | h
  · exact actualChartOverlap_circleIntegral_radius_le p g s r R hr h htarget_R
  · exact (actualChartOverlap_circleIntegral_radius_le p g s R r hR h htarget_r).symm

noncomputable def actualOverlapContourPairing
    (p : E) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt ℂ p) p) R ⊆ (chartAt ℂ p).target) :
    SameAtlasRRLocal.HolOn
      (SameAtlasRRLocal.overlapOpen p (SameAtlasRRLocal.chartSourceOpen p)) →ₗ[ℂ]
      Module.Dual ℂ (ActualCanonicalSection E) where
  toFun g := {
    toFun := fun s => ∮ z in C((chartAt ℂ p) p, R), actualChartOverlapValue p g z *
      actualLocalOneForm s p z (fun _ : Fin 1 => (1 : ℂ))
    map_add' := by
      intro s t
      change (∮ z in C((chartAt ℂ p) p, R), actualChartOverlapValue p g z *
        actualLocalOneFormCoefficient p z (s + t)) = _
      simp only [map_add, mul_add]
      exact circleIntegral.integral_add
        (actualChartOverlap_times_section_circleIntegrable p g s R hR htarget)
        (actualChartOverlap_times_section_circleIntegrable p g t R hR htarget)
    map_smul' := by
      intro c s
      change (∮ z in C((chartAt ℂ p) p, R), actualChartOverlapValue p g z *
        actualLocalOneFormCoefficient p z (c • s)) = _
      simp only [map_smul, smul_eq_mul, mul_left_comm _ c]
      exact circleIntegral.integral_const_mul _ _ _ _ }
  map_add' g h := by
    ext s
    change (∮ z in C((chartAt ℂ p) p, R), actualChartOverlapEvaluation p z (g + h) *
      actualLocalOneForm s p z (fun _ : Fin 1 => (1 : ℂ))) = _
    simp only [map_add, add_mul]
    exact circleIntegral.integral_add
      (actualChartOverlap_times_section_circleIntegrable p g s R hR htarget)
      (actualChartOverlap_times_section_circleIntegrable p h s R hR htarget)
  map_smul' c g := by
    ext s
    change (∮ z in C((chartAt ℂ p) p, R), actualChartOverlapEvaluation p z (c • g) *
      actualLocalOneForm s p z (fun _ : Fin 1 => (1 : ℂ))) = _
    simp only [map_smul, smul_eq_mul, mul_assoc]
    exact circleIntegral.integral_const_mul _ _ _ _

theorem actualOverlapContourPairing_radius_independent
    (p : E) (r R : ℝ) (hr : 0 < r) (hR : 0 < R)
    (htarget_r : Metric.closedBall ((chartAt ℂ p) p) r ⊆ (chartAt ℂ p).target)
    (htarget_R : Metric.closedBall ((chartAt ℂ p) p) R ⊆ (chartAt ℂ p).target) :
    actualOverlapContourPairing p R hR htarget_R =
      actualOverlapContourPairing p r hr htarget_r := by
  ext g s
  exact actualChartOverlap_circleIntegral_radius_independent p g s r R hr hR
    htarget_r htarget_R

theorem actualChartResidueRadius_exists (p : E) :
    ∃ R : ℝ, 0 < R ∧
      Metric.closedBall ((chartAt ℂ p) p) R ⊆ (chartAt ℂ p).target := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    ((chartAt ℂ p).open_target.mem_nhds
      ((chartAt ℂ p).map_source (mem_chart_source ℂ p)))
  refine ⟨ε / 2, half_pos hε, fun z hz => hball ?_⟩
  exact lt_of_le_of_lt hz (half_lt_self hε)

noncomputable def actualChartResidueRadius (p : E) : ℝ :=
  Classical.choose (actualChartResidueRadius_exists p)

theorem actualChartResidueRadius_pos (p : E) : 0 < actualChartResidueRadius p :=
  (Classical.choose_spec (actualChartResidueRadius_exists p)).1

theorem actualChartResidueRadius_target (p : E) :
    Metric.closedBall ((chartAt ℂ p) p) (actualChartResidueRadius p) ⊆
      (chartAt ℂ p).target :=
  (Classical.choose_spec (actualChartResidueRadius_exists p)).2

end Local

end CanonicalDimensionTwo
