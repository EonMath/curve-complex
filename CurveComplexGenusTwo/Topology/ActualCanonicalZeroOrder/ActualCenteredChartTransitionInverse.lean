import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.Complex.Basic

open scoped Manifold ContDiff Topology
open Filter

theorem actual_centered_chart_transition_local_inverse
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (q r : E) (hqr : q ∈ (chartAt ℂ r).source) :
    let h : ℂ → ℂ := fun w =>
      (chartAt ℂ r) ((chartAt ℂ q).symm ((chartAt ℂ q) q + w)) -
        (chartAt ℂ r) q;
    let k : ℂ → ℂ := fun w =>
      (chartAt ℂ q) ((chartAt ℂ r).symm ((chartAt ℂ r) q + w)) -
        (chartAt ℂ q) q;
    h 0 = 0 ∧ k 0 = 0 ∧
      (fun w => k (h w)) =ᶠ[𝓝 (0 : ℂ)] id ∧
      (fun w => h (k w)) =ᶠ[𝓝 (0 : ℂ)] id := by
  let cq := chartAt ℂ q
  let cr := chartAt ℂ r
  let h : ℂ → ℂ := fun w => cr (cq.symm (cq q + w)) - cr q
  let k : ℂ → ℂ := fun w => cq (cr.symm (cr q + w)) - cq q
  have hqsource : q ∈ cq.source := mem_chart_source ℂ q
  have hqt : cq q ∈ cq.target := cq.map_source hqsource
  have hrt : cr q ∈ cr.target := cr.map_source hqr
  have h0 : h 0 = 0 := by simp [h, cq.left_inv hqsource]
  have k0 : k 0 = 0 := by simp [k, cr.left_inv hqr]
  have htq : Tendsto (fun w : ℂ => cq q + w) (𝓝 (0 : ℂ)) (𝓝 (cq q)) := by
    have hcont : Continuous (fun w : ℂ => cq q + w) :=
      continuous_const.add continuous_id
    simpa only [add_zero] using (hcont.continuousAt (x := (0 : ℂ))).tendsto
  have htr : Tendsto (fun w : ℂ => cr q + w) (𝓝 (0 : ℂ)) (𝓝 (cr q)) := by
    have hcont : Continuous (fun w : ℂ => cr q + w) :=
      continuous_const.add continuous_id
    simpa only [add_zero] using (hcont.continuousAt (x := (0 : ℂ))).tendsto
  have hnearq : ∀ᶠ w : ℂ in 𝓝 (0 : ℂ),
      cq q + w ∈ cq.target ∧ cq.symm (cq q + w) ∈ cr.source := by
    have hsymm : Tendsto cq.symm (𝓝 (cq q)) (𝓝 q) :=
      by simpa only [cq.left_inv hqsource] using (cq.continuousAt_symm hqt).tendsto
    filter_upwards [htq.eventually (cq.open_target.mem_nhds hqt),
      (hsymm.comp htq).eventually (cr.open_source.mem_nhds hqr)] with w hw1 hw2
    exact ⟨hw1, hw2⟩
  have hnearr : ∀ᶠ w : ℂ in 𝓝 (0 : ℂ),
      cr q + w ∈ cr.target ∧ cr.symm (cr q + w) ∈ cq.source := by
    have hsymm : Tendsto cr.symm (𝓝 (cr q)) (𝓝 q) :=
      by simpa only [cr.left_inv hqr] using (cr.continuousAt_symm hrt).tendsto
    filter_upwards [htr.eventually (cr.open_target.mem_nhds hrt),
      (hsymm.comp htr).eventually (cq.open_source.mem_nhds hqsource)] with w hw1 hw2
    exact ⟨hw1, hw2⟩
  refine ⟨h0, k0, ?_, ?_⟩
  · filter_upwards [hnearq] with w hw
    let y := cq.symm (cq q + w)
    have hyq : cq y = cq q + w := cq.right_inv hw.1
    have hyr : cr.symm (cr y) = y := cr.left_inv hw.2
    change cq (cr.symm (cr q + (cr y - cr q))) - cq q = w
    have hadd : cr q + (cr y - cr q) = cr y := by abel
    rw [hadd, hyr, hyq]
    abel
  · filter_upwards [hnearr] with w hw
    let y := cr.symm (cr q + w)
    have hyr : cr y = cr q + w := cr.right_inv hw.1
    have hyq : cq.symm (cq y) = y := cq.left_inv hw.2
    change cr (cq.symm (cq q + (cq y - cq q))) - cr q = w
    have hadd : cq q + (cq y - cq q) = cq y := by abel
    rw [hadd, hyq, hyr]
    abel

#print axioms actual_centered_chart_transition_local_inverse
