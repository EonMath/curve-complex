import CurveComplexGenusTwo.Topology.ActualJointGeodesicMinimum.Providers
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.OriginalLoopDefinitions
import CurveComplexGenusTwo.Foundations.FoundationsIntersectionPort
import CurveComplexGenusTwo.Dictionary.Genus
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Homotopy.Lifting
import CurveComplexGenusTwo.Topology.ActualJointGeodesicMinimum.GeodesicImageClassInvariance
import CurveComplexGenusTwo.Topology.ActualJointGeodesicMinimum.GeodesicMinimumCount

namespace CurveComplex.Hyperbolic.JointMinimum
open Set Topology CurveComplex.LocalSurgery
open scoped Manifold UpperHalfPlane
section Surface
variable {E : Type} [TopologicalSpace E]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem fixed_classes_have_joint_invariant_minimum_pair
    (H : ClosedHyperbolicMetric E) (hE : IsGenus E 2)
    (τ : E ≃ₜ E) (hτ : letI : MetricSpace E := H.metric; Isometry τ)
    (c₀ d₀ : EssentialCurve E)
    (hclasses : Quotient.mk (essentialCurveSetoid E) c₀ ≠
      Quotient.mk (essentialCurveSetoid E) d₀)
    (htransverse : Transverse c₀.val d₀.val)
    (hminimum : (c₀.val.image ∩ d₀.val.image).ncard =
      geometricIntersection (Quotient.mk (essentialCurveSetoid E) c₀)
        (Quotient.mk (essentialCurveSetoid E) d₀))
    (hcτ : AmbientIsotopy.Rel (τ '' c₀.val.image) c₀.val.image)
    (hdτ : AmbientIsotopy.Rel (τ '' d₀.val.image) d₀.val.image) :
    ∃ c d : EssentialCurve E,
      Quotient.mk (essentialCurveSetoid E) c =
        Quotient.mk (essentialCurveSetoid E) c₀ ∧
      Quotient.mk (essentialCurveSetoid E) d =
        Quotient.mk (essentialCurveSetoid E) d₀ ∧
      τ '' c.val.image = c.val.image ∧
      τ '' d.val.image = d.val.image ∧
      Transverse c.val d.val ∧
      (c.val.image ∩ d.val.image).ncard = (c₀.val.image ∩ d₀.val.image).ncard := by
  obtain ⟨c, hc, hcgeo, hcinv⟩ :=
    fixed_class_has_invariant_geodesic_representative H hE τ hτ c₀ hcτ
  obtain ⟨d, hd, hdgeo, hdinv⟩ :=
    fixed_class_has_invariant_geodesic_representative H hE τ hτ d₀ hdτ
  have hne : c.val.image ≠ d.val.image := by
    intro heq
    have hrel : AmbientIsotopy.Rel c.val.image d.val.image := by
      rw [← heq]
      exact ambientIsotopy_equivalence.refl _
    exact hclasses (hc.symm.trans ((Quotient.sound hrel).trans hd))
  obtain ⟨ht, hcount⟩ :=
    distinct_geodesic_essential_curves_realize_minimum_genus_two H hE c d hcgeo hdgeo hne
  refine ⟨c, d, hc, hd, hcinv, hdinv, ht, ?_⟩
  rw [hc, hd] at hcount
  exact hcount.trans hminimum.symm

end Surface
end CurveComplex.Hyperbolic.JointMinimum
