import CurveComplexGenusTwo.Topology.ActualSmoothMorseNormalForm.ActualSameAtlasRealSmooth
import CurveComplexGenusTwo.Topology.ActualSmoothMorseNormalForm.ActualLocalTangentPerturbation
import CurveComplexGenusTwo.Topology.ActualCanonicalZeroOrder.ActualSameAtlasReferenceFieldVZD
import CurveComplexGenusTwo.Dictionary.Genus

open scoped Manifold ContDiff Bundle
open Bundle

theorem actual_same_atlas_genus_two_reference_VZD
    (E : Type) [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (hg : CurveComplex.IsGenus E 2) (A : ChartedSpace ℂ E)
    (hA : letI : ChartedSpace ℂ E := A; IsManifold 𝓘(ℂ) ∞ E) :
    letI : ChartedSpace ℂ E := A;
    letI : IsManifold 𝓘(ℂ) ∞ E := hA;
    ∃ hR : IsManifold 𝓘(ℝ,ℂ) ∞ E,
    letI : IsManifold 𝓘(ℝ,ℂ) ∞ E := hR;
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
  letI : ChartedSpace ℂ E := A
  let : IsManifold 𝓘(ℂ) ∞ E := hA
  let hR : IsManifold 𝓘(ℝ,ℂ) ∞ E := actual_same_atlas_complex_is_real_smooth E hA
  refine ⟨hR, ?_⟩
  letI : IsManifold 𝓘(ℝ,ℂ) ∞ E := hR
  letI : CurveComplex.ClosedSurface E := Classical.choice hg.2.1
  obtain ⟨ι, cover, hfinite, hcompact, hsource, hcover⟩ :=
    actual_same_atlas_finite_compact_bump_cores E hg A hA
  letI : Fintype ι := cover.fintype
  exact actual_finite_bump_cover_reference_field_VZD cover
    (fun i x hx => hsource i hx) hcover

#print axioms actual_same_atlas_genus_two_reference_VZD
