import CurveComplexGenusTwo.Dictionary.Genus
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

open scoped Manifold ContDiff

theorem actual_same_atlas_complex_is_real_smooth
    (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E]
    (hA : IsManifold 𝓘(ℂ) ∞ E) : IsManifold 𝓘(ℝ,ℂ) ∞ E := by
  let : IsManifold 𝓘(ℂ) ∞ E := hA
  apply isManifold_of_contDiffOn
  intro e e' he he'
  have hh := StructureGroupoid.compatible (contDiffGroupoid ∞ 𝓘(ℂ)) he he'
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hh
  simpa only [contDiffPregroupoid, mfld_simps] using hh.1.restrict_scalars ℝ

#print axioms actual_same_atlas_complex_is_real_smooth
