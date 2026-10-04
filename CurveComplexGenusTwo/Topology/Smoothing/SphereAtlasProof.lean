import CurveComplexGenusTwo.Dictionary.MarkedSphere
import CurveComplexGenusTwo.Topology.Smoothing.AtlasTransport

/-! Source: references/curve-complex-genus-two.pdf, §§2.2–2.4.
Fresh scaffolds after the V2 source review rejection. No existing statement is
revised. Atlas choice is an output, not an extra premise on the actual model. -/

namespace CurveComplex.HyperellipticModel

open scoped Manifold ContDiff

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- A chosen smooth atlas for the existing topology of the downstairs sphere.
The atlas is data, so no arbitrary ambient `ChartedSpace S` is fixed. -/
structure SphereSmoothAtlas (S : Type) [TopologicalSpace S] where
  charts : ChartedSpace (EuclideanSpace ℝ (Fin 2)) S
  manifold : letI := charts; IsManifold (𝓡 2) ∞ S

/-- The topology already supplied by `M.sphere` admits a smooth sphere atlas.
This is an obligation, not an assertion about a pre-existing sphere atlas. -/
theorem sphere_smooth_atlas_exists (M : HyperellipticModel E S) :
    Nonempty (SphereSmoothAtlas S) := by
  letI : IsManifold (𝓡 2) ∞ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    IsManifold.of_le (n := ω) le_top
  exact ⟨⟨transportedCharts M.sphere, transportedCharts_isManifold (𝓡 2) ∞ M.sphere⟩⟩

/-- The chosen atlas used by the actual arc-model presentation. -/
noncomputable def actualSphereSmoothAtlas (M : HyperellipticModel E S) :
    SphereSmoothAtlas S := Classical.choice (sphere_smooth_atlas_exists M)


#print axioms sphere_smooth_atlas_exists
#print axioms actualSphereSmoothAtlas
end CurveComplex.HyperellipticModel
