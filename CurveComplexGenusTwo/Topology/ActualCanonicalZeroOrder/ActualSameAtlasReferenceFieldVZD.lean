import CurveComplexGenusTwo.Topology.ActualCanonicalZeroOrder.ActualFiniteTangentCoreField
import CurveComplexGenusTwo.Topology.ActualCanonicalZeroOrder.ActualLiteralRegularDerivativeTransfer
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualLiteralTangentCoefficientSmooth
import CurveComplexGenusTwo.Topology.ActualCanonicalZeroOrder.ActualLiteralZeroIsolation

open scoped Manifold ContDiff Bundle
open Bundle

theorem actual_finite_bump_cover_reference_field_VZD
    {E ι : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [T2Space E] [CompactSpace E] [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    [Fintype ι]
    (cover : SmoothBumpCovering ι 𝓘(ℝ,ℂ) E Set.univ)
    (hsource : ∀ i (x : E), cover i x = 1 →
      x ∈ (chartAt ℂ (cover.c i)).source)
    (hcover : ∀ x : E, ∃ i, cover i x = 1) :
    ∃ V : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x,
      ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
        (fun x => TotalSpace.mk' ℂ x (V x)) ∧
      ∃ Z : Finset E, (Z : Set E) = {x | V x = 0} ∧
      ∃ D : Z → (ℂ ≃L[ℝ] ℂ),
        ∀ q : Z, HasFDerivAt
          (fun w : ℂ =>
            let x := (chartAt ℂ q.val).symm ((chartAt ℂ q.val) q.val + w)
            (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q.val
              (TotalSpace.mk' ℂ x (V x))).2)
          (D q).toContinuousLinearMap 0 := by
  classical
  obtain ⟨V, hV, hcore⟩ := actual_finite_bump_cover_regular_tangent_field cover hsource
  have hD (q : E) (hq : V q = 0) :
      ∃ T : ℂ ≃L[ℝ] ℂ,
        HasFDerivAt
          (fun w : ℂ =>
            let x := (chartAt ℂ q).symm ((chartAt ℂ q) q + w)
            (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q
              (TotalSpace.mk' ℂ x (V x))).2)
          T.toContinuousLinearMap 0 := by
    obtain ⟨i, hi⟩ := hcover q
    exact actual_literal_regular_derivative_transfer V hV q (cover.c i)
      (hsource i q hi) hq (hcore i q hi hq)
  obtain ⟨Z, hZ⟩ := actual_literal_nondegenerate_tangent_zeros_finite V hV
    (fun q _ => actual_literal_tangent_coefficient_smooth V hV q) hD
  let D : Z → (ℂ ≃L[ℝ] ℂ) := fun q =>
    Classical.choose (hD q.val (by
      have hz : (q.val : E) ∈ (Z : Set E) := q.property
      rw [hZ] at hz
      exact hz))
  refine ⟨V, hV, Z, hZ, D, ?_⟩
  intro q
  exact (Classical.choose_spec (hD q.val (by
    have hz : (q.val : E) ∈ (Z : Set E) := q.property
    rw [hZ] at hz
    exact hz)))

#print axioms actual_finite_bump_cover_reference_field_VZD
