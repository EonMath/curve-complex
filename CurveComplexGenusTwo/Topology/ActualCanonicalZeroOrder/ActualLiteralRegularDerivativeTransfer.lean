import CurveComplexGenusTwo.Topology.ActualCanonicalZeroOrder.ActualOriginalChartDerivativeEquiv
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualRealTangentTransitionDifferentiable
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualRealTangentTransitionEventually
import CurveComplexGenusTwo.Topology.ActualCanonicalZeroOrder.ActualZeroDerivativeTransportRule
import CurveComplexGenusTwo.Topology.ActualCanonicalZeroOrder.ActualTangentChartCoefficientOn
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Normed.Module.FiniteDimension

open scoped Manifold ContDiff Bundle Topology
open Bundle Filter

theorem actual_literal_regular_derivative_transfer
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (W : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (hW : ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (W x)))
    (q r : E) (hqr : q ∈ (chartAt ℂ r).source)
    (hWq : W q = 0)
    (hdet : (fderiv ℝ
      (fun z : ℂ =>
        let x := (chartAt ℂ r).symm z
        (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) r
          (TotalSpace.mk' ℂ x (W x))).2)
      ((chartAt ℂ r) q)).det ≠ 0) :
    ∃ T : ℂ ≃L[ℝ] ℂ,
      HasFDerivAt
        (fun w : ℂ =>
          let x := (chartAt ℂ q).symm ((chartAt ℂ q) q + w)
          (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q
            (TotalSpace.mk' ℂ x (W x))).2)
        T.toContinuousLinearMap 0 := by
  let cq := chartAt ℂ q
  let cr := chartAt ℂ r
  let eq := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q
  let er := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) r
  let raw : ℂ → ℂ := fun z =>
    (er (TotalSpace.mk' ℂ (cr.symm z) (W (cr.symm z)))).2
  let Fr : ℂ → ℂ := fun w => raw (cr q + w)
  let Fq : ℂ → ℂ := fun w =>
    let x := cq.symm (cq q + w)
    (eq (TotalSpace.mk' ℂ x (W x))).2
  let h : ℂ → ℂ := fun w => cr (cq.symm (cq q + w)) - cr q
  let A : ℂ → ℂ →L[ℝ] ℂ := fun w => er.coordChangeL ℝ eq (cq.symm (cq q + w))
  let L : ℂ ≃L[ℝ] ℂ := er.coordChangeL ℝ eq q
  have hcrq : cr q ∈ cr.target := cr.map_source hqr
  have hraw : ContDiffAt ℝ 1 raw (cr q) :=
    (actual_tangent_chart_coefficient_contDiffOn W hW r
      (cr q) hcrq).contDiffAt (cr.open_target.mem_nhds hcrq)
  let D : ℂ ≃L[ℝ] ℂ :=
    (LinearMap.equivOfDetNeZero (fderiv ℝ raw (cr q)).toLinearMap hdet).toContinuousLinearEquiv
  have hD : D.toContinuousLinearMap = fderiv ℝ raw (cr q) := by
    ext z
    simp [D]
  have hrawD : HasFDerivAt raw D.toContinuousLinearMap (cr q) := by
    rw [hD]
    exact (hraw.differentiableAt (by norm_num)).hasFDerivAt
  have hshift : HasFDerivAt (fun w : ℂ => cr q + w)
      (ContinuousLinearMap.id ℝ ℂ) 0 := by
    have hs := (hasFDerivAt_const (x := (0 : ℂ)) (cr q)).add
      (hasFDerivAt_id (𝕜 := ℝ) (0 : ℂ))
    convert hs using 1
    funext w
    rfl
    simp
  have hrawD' : HasFDerivAt raw D.toContinuousLinearMap (cr q + (0 : ℂ)) :=
    by simpa using hrawD
  have hFr : HasFDerivAt Fr D.toContinuousLinearMap 0 := by
    have hc := hrawD'.comp 0 hshift
    simpa only [Fr, Function.comp_def, ContinuousLinearMap.comp_id] using hc
  have hFr0 : Fr 0 = 0 := by
    have hbase : q ∈ er.baseSet := by simpa [er] using hqr
    have hback : cr.symm (cr q) = q := cr.left_inv hqr
    change (er (TotalSpace.mk' ℂ (cr.symm (cr q + 0)) (W (cr.symm (cr q + 0))))).2 = 0
    rw [add_zero, hback, hWq]
    rw [← er.continuousLinearMapAt_apply_of_mem (R := ℝ) hbase]
    simp
  obtain ⟨H, hh⟩ := actual_original_chart_transition_derivative_equiv q r hqr
  have hA : DifferentiableAt ℝ A 0 :=
    actual_real_tangent_transition_differentiable q r hqr
  have hA0 : A 0 = L.toContinuousLinearMap := by
    have hback : cq.symm (cq q) = q := cq.left_inv (mem_chart_source ℂ q)
    simp only [A, L, add_zero, hback]
  have hEq : Fq =ᶠ[𝓝 (0 : ℂ)] (fun w => A w (Fr (h w))) :=
    actual_real_tangent_transition_eventually q r hqr W
  obtain ⟨T, hT⟩ := actual_zero_derivative_transport_rule A Fr h hA L D H
    hA0 hFr hFr0 hh (by
      have hback : cq.symm (cq q) = q := cq.left_inv (mem_chart_source ℂ q)
      simp [h, hback])
  exact ⟨T, hT.congr_of_eventuallyEq hEq⟩

#print axioms actual_literal_regular_derivative_transfer
