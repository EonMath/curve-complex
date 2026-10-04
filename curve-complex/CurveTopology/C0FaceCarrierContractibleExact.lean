import C0FaceUniversalCurveExact
open Set Topology CurveComplex
open scoped Manifold ContDiff
attribute [local instance] instDecidable_originalArcFaceCurveCarriers
set_option autoImplicit false
namespace CurveComplexGenusTwo.SourceTopology.OriginalArcFaceCarriers
open OriginalBoundaryArc
variable (S : Type) [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (x : S) (R : ℝ)

theorem nonempty_small_faceCarrier_contractible
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (τ : Finset (ArcVertex S x R)) (hτ : τ ∈ (arcComplex S x R).faces)
    (hcard : τ.card ≤ 3) :
    ContractibleSpace (RealizationPoint
      (fullSubcomplex (curveComplex S 0) (faceCarrier S x R τ))) := by
  classical
  have huniversal : ∃ c : EssentialCurve S,
      faceCarrier S x R τ (Quotient.mk (essentialCurveSetoid S) c) ∧
      ∀ v : Vertex S, faceCarrier S x R τ v →
        geometricIntersection (Quotient.mk (essentialCurveSetoid S) c) v = 0 := by
    exact nonempty_small_faceCarrier_has_universal_curve S x R g hg hS hR htarget τ hτ hcard
  obtain ⟨c, hc, hcompat⟩ := huniversal
  let a : {v : Vertex S // faceCarrier S x R τ v} :=
    ⟨Quotient.mk (essentialCurveSetoid S) c, hc⟩
  apply coneApex_contractible _ a
  intro σ hσ
  change (insert a σ).image Subtype.val ∈ (curveComplex S 0).faces
  rw [Finset.image_insert]
  change (insert a.val (σ.image Subtype.val)).Nonempty ∧
    ∀ α ∈ insert a.val (σ.image Subtype.val),
      ∀ β ∈ insert a.val (σ.image Subtype.val),
        α ≠ β → geometricIntersection α β ≤ 0
  refine ⟨Finset.insert_nonempty _ _, ?_⟩
  intro α hα β hβ hne
  rcases Finset.mem_insert.mp hα with rfl | hα
  · rcases Finset.mem_insert.mp hβ with rfl | hβ
    · exact (hne rfl).elim
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hβ
      exact le_of_eq (hcompat v.val v.property)
  · rcases Finset.mem_insert.mp hβ with rfl | hβ
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hα
      rw [geometricIntersection_symm_of_chart]
      exact le_of_eq (hcompat v.val v.property)
    · exact hσ.2 α hα β hβ hne

end CurveComplexGenusTwo.SourceTopology.OriginalArcFaceCarriers
