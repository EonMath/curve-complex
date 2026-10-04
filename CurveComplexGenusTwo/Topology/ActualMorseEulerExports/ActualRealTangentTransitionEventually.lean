import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualRealTangentTransitionCoefficient
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.Complex.Basic

open scoped Manifold ContDiff Bundle Topology
open Bundle Filter

theorem actual_real_tangent_transition_eventually
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (q r : E) (hqr : q ∈ (chartAt ℂ r).source)
    (W : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x) :
    let cq := chartAt ℂ q;
    let cr := chartAt ℂ r;
    let eq := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q;
    let er := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) r;
    let y : ℂ → E := fun w => cq.symm (cq q + w);
    let h : ℂ → ℂ := fun w => cr (y w) - cr q;
    let A : ℂ → ℂ →L[ℝ] ℂ := fun w => er.coordChangeL ℝ eq (y w);
    let Fq : ℂ → ℂ := fun w => (eq (TotalSpace.mk' ℂ (y w) (W (y w)))).2;
    let Fr : ℂ → ℂ := fun w =>
      let x := cr.symm (cr q + w)
      (er (TotalSpace.mk' ℂ x (W x))).2;
    Fq =ᶠ[𝓝 (0 : ℂ)] (fun w => A w (Fr (h w))) := by
  let cq := chartAt ℂ q
  let cr := chartAt ℂ r
  let eq := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q
  let er := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) r
  let y : ℂ → E := fun w => cq.symm (cq q + w)
  let h : ℂ → ℂ := fun w => cr (y w) - cr q
  let A : ℂ → ℂ →L[ℝ] ℂ := fun w => er.coordChangeL ℝ eq (y w)
  let Fq : ℂ → ℂ := fun w => (eq (TotalSpace.mk' ℂ (y w) (W (y w)))).2
  let Fr : ℂ → ℂ := fun w =>
    let x := cr.symm (cr q + w)
    (er (TotalSpace.mk' ℂ x (W x))).2
  have hqsource : q ∈ cq.source := mem_chart_source ℂ q
  have hqt : cq q ∈ cq.target := cq.map_source hqsource
  have htq : Tendsto (fun w : ℂ => cq q + w) (𝓝 (0 : ℂ)) (𝓝 (cq q)) := by
    have hcont : Continuous (fun w : ℂ => cq q + w) :=
      continuous_const.add continuous_id
    simpa only [add_zero] using (hcont.continuousAt (x := (0 : ℂ))).tendsto
  have hy : Tendsto y (𝓝 (0 : ℂ)) (𝓝 q) := by
    have hc : Tendsto cq.symm (𝓝 (cq q)) (𝓝 q) := by
      simpa only [cq.left_inv hqsource] using (cq.continuousAt_symm hqt).tendsto
    exact hc.comp htq
  have hnear : ∀ᶠ w : ℂ in 𝓝 (0 : ℂ),
      cq q + w ∈ cq.target ∧ y w ∈ cr.source := by
    filter_upwards [htq.eventually (cq.open_target.mem_nhds hqt),
      hy.eventually (cr.open_source.mem_nhds hqr)] with w hw1 hw2
    exact ⟨hw1, hw2⟩
  filter_upwards [hnear] with w hw
  have hyq : y w ∈ cq.source := cq.map_target hw.1
  have hyr : y w ∈ cr.source := hw.2
  have hback : cr.symm (cr q + h w) = y w := by
    have hadd : cr q + (cr (y w) - cr q) = cr (y w) := by abel
    change cr.symm (cr q + (cr (y w) - cr q)) = y w
    rw [hadd, cr.left_inv hyr]
  have hcoef := actual_real_tangent_transition_coefficient q r (y w) hyq hyr W
  change (eq ⟨y w, W (y w)⟩).2 =
    (er.coordChangeL ℝ eq (y w))
      (er ⟨cr.symm (cr q + h w), W (cr.symm (cr q + h w))⟩).2
  rw [hback]
  exact hcoef.symm

