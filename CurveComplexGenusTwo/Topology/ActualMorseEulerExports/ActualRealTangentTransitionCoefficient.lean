import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Analysis.Complex.Basic

open scoped Manifold ContDiff Bundle
open Bundle

theorem actual_real_tangent_transition_coefficient
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (q r y : E) (hyq : y ∈ (chartAt ℂ q).source)
    (hyr : y ∈ (chartAt ℂ r).source)
    (W : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x) :
    let eq := trivializationAt ℂ (fun x : E => TangentSpace 𝓘(ℝ,ℂ) x) q;
    let er := trivializationAt ℂ (fun x : E => TangentSpace 𝓘(ℝ,ℂ) x) r;
    (er.coordChangeL ℝ eq y) (er (TotalSpace.mk' ℂ y (W y))).2 =
      (eq (TotalSpace.mk' ℂ y (W y))).2 := by
  let eq := trivializationAt ℂ (fun x : E => TangentSpace 𝓘(ℝ,ℂ) x) q
  let er := trivializationAt ℂ (fun x : E => TangentSpace 𝓘(ℝ,ℂ) x) r
  have hyqe : y ∈ eq.baseSet := by simpa [eq] using hyq
  have hyre : y ∈ er.baseSet := by simpa [er] using hyr
  change (er.coordChangeL ℝ eq y) (er ⟨y, W y⟩).2 = (eq ⟨y, W y⟩).2
  rw [← er.continuousLinearMapAt_apply_of_mem (R := ℝ) hyre]
  rw [er.coordChangeL_apply eq ⟨hyre, hyqe⟩]
  rw [← er.symmL_apply (R := ℝ) hyre]
  rw [er.symmL_continuousLinearMapAt hyre]

