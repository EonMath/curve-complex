import C0FaceAlignmentExact

open Set Topology CurveComplex
open scoped Manifold ContDiff
set_option autoImplicit false

namespace CurveComplexGenusTwo.SourceTopology.OriginalArcFaceCarriers
open OriginalBoundaryArc
variable (S : Type) [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (x : S) (R : ℝ)

theorem faceCarrier_eq_actualFamilyCarrier
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (τ : Finset (ArcVertex S x R)) (hτ : τ ∈ (arcComplex S x R).faces)
    (r : SimultaneousRepresentatives S x R τ) :
    faceCarrier S x R τ = actualFamilyCarrier S x R r.arc := by
  classical
  funext v
  apply propext
  constructor
  · rintro ⟨a, c, hcv, hcQ, hca⟩
    obtain ⟨H, hB, hfinal⟩ :=
      simultaneousRepresentatives_alignment S x R g hg hS hR htarget τ hτ a r
    obtain ⟨d, _, hdc, hdQ, hda⟩ :=
      original_Q_motion_transports_avoiding_curve S x R g hg hS hR htarget
        ↥τ a.arc r.arc H hB hfinal c hcQ hca
    exact ⟨d, hdc.trans hcv, hdQ, hda⟩
  · intro hv
    exact ⟨r, hv⟩


end CurveComplexGenusTwo.SourceTopology.OriginalArcFaceCarriers
