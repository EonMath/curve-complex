import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualTwoMetricSheetsCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.MetricChartLocalAreaCandidate

namespace CurveComplex.Hyperbolic
open Set Topology MeasureTheory
open scoped NNReal ENNReal MeasureTheory

set_option maxHeartbeats 1000000 in
theorem actual_unramified_local_cover_normalized_area {E S B : Type}
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace S] [T2Space S]
    [MetricSpace B] [MeasurableSpace B] [BorelSpace B]
    (q : BranchedDoubleCover E S) (identify : S ≃ₜ B)
    (hlocal : ∀ x : E, x ∉ q.ramification → ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ∀ z ∈ U, dist y z = dist (identify (q.projection y)) (identify (q.projection z)))
    (b : S) (hb : b ∉ (q.branch : Set S)) :
    ∃ V : Set B, IsOpen V ∧ identify b ∈ V ∧ V ⊆ (identify '' (q.branch : Set S))ᶜ ∧
      ∀ s : Set B, MeasurableSet s → s ⊆ V →
        (μHE[2] : Measure E) ((fun x => identify (q.projection x)) ⁻¹' s) =
          2 * (μHE[2] : Measure B) s := by
  obtain ⟨U, hU, hbU, hUavoid, e₁, e₂, ht₁, ht₂, hdisj, hpre, he₁, he₂, hm₁, hm₂⟩ :=
    q.actual_two_metric_sheets (inferInstance : MetricSpace E) rfl identify hlocal b hb
  let V := identify '' U
  let p : E → B := fun x => identify (q.projection x)
  have hp : Continuous p := identify.continuous.comp q.projection_continuous
  let f₁ := e₁.transHomeomorph identify
  let f₂ := e₂.transHomeomorph identify
  have hf₁ : f₁.target = V := by
    ext z
    change identify.symm z ∈ e₁.target ↔ z ∈ identify '' U
    rw [ht₁]
    constructor
    · intro hz; exact ⟨identify.symm z, hz, identify.apply_symm_apply z⟩
    · rintro ⟨y, hy, rfl⟩; simpa using hy
  have hf₂ : f₂.target = V := by
    ext z
    change identify.symm z ∈ e₂.target ↔ z ∈ identify '' U
    rw [ht₂]
    constructor
    · intro hz; exact ⟨identify.symm z, hz, identify.apply_symm_apply z⟩
    · rintro ⟨y, hy, rfl⟩; simpa using hy
  have hfp₁ (x : E) : f₁ x = p x := congrArg identify (he₁ x)
  have hfp₂ (x : E) : f₂ x = p x := congrArg identify (he₂ x)
  refine ⟨V, identify.isOpenMap U hU, ⟨b, hbU, rfl⟩, ?_, ?_⟩
  · rintro z ⟨b', hb', rfl⟩ ⟨c, hc, heq⟩
    have hbc : c = b' := identify.injective heq
    subst c
    exact hUavoid hb' hc
  · intro s hs hsV
    let s₁ := e₁.source ∩ p ⁻¹' s
    let s₂ := e₂.source ∩ p ⁻¹' s
    have hs₁ : MeasurableSet s₁ := e₁.open_source.measurableSet.inter (hs.preimage hp.measurable)
    have hs₂ : MeasurableSet s₂ := e₂.open_source.measurableSet.inter (hs.preimage hp.measurable)
    have hds : Disjoint s₁ s₂ := hdisj.mono inter_subset_left inter_subset_left
    have hunion : s₁ ∪ s₂ = p ⁻¹' s := by
      ext x; constructor
      · rintro (hx | hx); exact hx.2; exact hx.2
      · intro hx
        obtain ⟨c, hc, heq⟩ := hsV hx
        have hqc : q.projection x = c := (identify.injective heq).symm
        have hxU : q.projection x ∈ U := hqc.symm ▸ hc
        have hxs : x ∈ e₁.source ∪ e₂.source := hpre ▸ hxU
        rcases hxs with hx₁ | hx₂
        · exact Or.inl ⟨hx₁, hx⟩
        · exact Or.inr ⟨hx₂, hx⟩
    have him₁ : f₁ '' s₁ = s := by
      ext z; constructor
      · rintro ⟨x, hx, rfl⟩
        rw [hfp₁]
        exact hx.2
      · intro hz
        have hzt : z ∈ f₁.target := hf₁.symm ▸ hsV hz
        refine ⟨f₁.symm z, ⟨f₁.map_target hzt, ?_⟩, f₁.right_inv hzt⟩
        change p (f₁.symm z) ∈ s
        rw [← hfp₁, f₁.right_inv hzt]
        exact hz
    have him₂ : f₂ '' s₂ = s := by
      ext z; constructor
      · rintro ⟨x, hx, rfl⟩
        rw [hfp₂]
        exact hx.2
      · intro hz
        have hzt : z ∈ f₂.target := hf₂.symm ▸ hsV hz
        refine ⟨f₂.symm z, ⟨f₂.map_target hzt, ?_⟩, f₂.right_inv hzt⟩
        change p (f₂.symm z) ∈ s
        rw [← hfp₂, f₂.right_inv hzt]
        exact hz
    have hmass₁ : (μHE[2] : Measure E) s₁ = (μHE[2] : Measure B) s := by
      have h := metric_chart_normalized_area_image f₁ hm₁ s₁ inter_subset_left
      rw [him₁] at h; exact h.symm
    have hmass₂ : (μHE[2] : Measure E) s₂ = (μHE[2] : Measure B) s := by
      have h := metric_chart_normalized_area_image f₂ hm₂ s₂ inter_subset_left
      rw [him₂] at h; exact h.symm
    rw [← hunion, measure_union hds hs₂, hmass₁, hmass₂, ← two_mul]

end CurveComplex.Hyperbolic
