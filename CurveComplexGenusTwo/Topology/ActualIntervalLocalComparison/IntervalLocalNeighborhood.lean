import CurveComplexGenusTwo.Topology.ActualIntervalLocalComparison.IntervalLocalRegularComparison

open scoped Manifold ContDiff Bundle Simplicial
open CanonicalDimensionTwo

namespace CanonicalDimensionTwo

theorem actualChartBallOpenSet_refines_open {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E]
    (U : Set E) (hU : IsOpen U) (x : E) (hx : x ∈ U) :
    ∃ r : ℝ, 0 < r ∧
      Metric.ball ((chartAt ℂ x) x) r ⊆ (chartAt ℂ x).target ∧
      x ∈ actualChartBallOpenSet x ((chartAt ℂ x) x) r ∧
      actualChartBallOpenSet x ((chartAt ℂ x) x) r ⊆ U := by
  let e := chartAt ℂ x
  have hsource : x ∈ e.source := mem_chart_source ℂ x
  have hcenter : e x ∈ e.target := e.map_source hsource
  have hopen : IsOpen (e.target ∩ e.symm ⁻¹' U) :=
    e.isOpen_inter_preimage_symm hU
  have hmem : e x ∈ e.target ∩ e.symm ⁻¹' U := by
    refine ⟨hcenter, ?_⟩
    change e.symm (e x) ∈ U
    rwa [e.left_inv hsource]
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen (e x) hmem
  refine ⟨r, hr, ?_, ?_, ?_⟩
  · intro y hy
    exact (hball hy).1
  · exact ⟨hsource, Metric.mem_ball_self hr⟩
  · intro y hy
    have hcoord := hball hy.2
    have himage : e.symm (e y) ∈ U := hcoord.2
    rwa [e.left_inv hy.1] at himage

theorem actualSmallRegularArcInOpen {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (U : Set E) (hU : IsOpen U) (x : E) (hx : x ∈ U) :
    ∃ r : ℝ, 0 < r ∧
      x ∈ actualChartBallOpenSet x ((chartAt ℂ x) x) r ∧
      ∀ y ∈ actualChartBallOpenSet x ((chartAt ℂ x) x) r,
        ∀ z ∈ actualChartBallOpenSet x ((chartAt ℂ x) x) r,
          ∃ γ : ActualRegularPath E,
            γ.toFun 0 = y ∧ γ.toFun 1 = z ∧
            ∀ t : ℝ, γ.toFun t ∈ U := by
  obtain ⟨r, hr, htarget, hcenter, hsubset⟩ :=
    actualChartBallOpenSet_refines_open U hU x hx
  refine ⟨r, hr, hcenter, ?_⟩
  intro y hy z hz
  let v : Metric.ball ((chartAt ℂ x) x) r := ⟨(chartAt ℂ x) y, hy.2⟩
  let w : Metric.ball ((chartAt ℂ x) x) r := ⟨(chartAt ℂ x) z, hz.2⟩
  let γ := actualChartBallRegularArc x ((chartAt ℂ x) x) r htarget v w
  refine ⟨γ, ?_, ?_, ?_⟩
  · change actualChartSmoothArc x ((chartAt ℂ x) x) r htarget v w 0 = y
    rw [actualChartSmoothArc_zero]
    exact (chartAt ℂ x).left_inv hy.1
  · change actualChartSmoothArc x ((chartAt ℂ x) x) r htarget v w 1 = z
    rw [actualChartSmoothArc_one]
    exact (chartAt ℂ x).left_inv hz.1
  · intro t
    apply hsubset
    exact ⟨actualChartSmoothArc_source x ((chartAt ℂ x) x) r htarget v w t,
      actualChartSmoothArc_chart_ball x ((chartAt ℂ x) x) r htarget v w t⟩

end CanonicalDimensionTwo
