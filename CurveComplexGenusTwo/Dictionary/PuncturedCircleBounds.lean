import CurveComplexGenusTwo.Dictionary.MarkedSphere
import CurveComplexGenusTwo.Topology.CapBandGeometry.GlobalSphereJordanHeaders

namespace CurveComplex
open Topology Set
namespace HyperellipticModel

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Transport the standard spherical embedded-circle disc producer through the
model homeomorphism `M.sphere`; the resulting disc bounds any punctured circle. -/
theorem puncturedCircle_boundsDisc
    (M : HyperellipticModel E S) (c : PuncturedCircle M) :
    BoundsDisc c.curve := by
  let d : Curve (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    { map := fun z => M.sphere (c.curve.map z)
      embedded := M.sphere.isEmbedding.comp c.curve.embedded }
  obtain ⟨F, hF, hboundary⟩ := CurveComplex.LocalSurgery.standard_sphere_embedded_circle_bounds_disc d
  refine ⟨⟨fun x => M.sphere.symm (F x),
      M.sphere.symm.continuous.comp F.continuous⟩,
    M.sphere.symm.isEmbedding.comp hF, ?_⟩
  change (M.sphere.symm ∘ (F : Metric.closedBall
    (0 : EuclideanSpace ℝ (Fin 2)) 1 → Metric.sphere
      (0 : EuclideanSpace ℝ (Fin 3)) 1)) ''
      {x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 |
        (x : EuclideanSpace ℝ (Fin 2)) ∈ Metric.sphere 0 1} = c.curve.image
  rw [Set.image_comp, hboundary]
  change M.sphere.symm '' Set.range
      (fun z : Circle => M.sphere (c.curve.map z)) = Set.range c.curve.map
  ext x
  constructor
  · rintro ⟨z, hz, hzx⟩
    rcases hz with ⟨w, hw⟩
    refine ⟨w, ?_⟩
    rw [← hzx, ← hw]
    change c.curve.map w = M.sphere.symm (M.sphere (c.curve.map w))
    exact (M.sphere.symm_apply_apply (c.curve.map w)).symm
  · rintro ⟨w, rfl⟩
    refine ⟨M.sphere (c.curve.map w), ⟨w, rfl⟩, ?_⟩
    exact M.sphere.symm_apply_apply (c.curve.map w)


end HyperellipticModel
end CurveComplex

#print axioms CurveComplex.HyperellipticModel.puncturedCircle_boundsDisc
