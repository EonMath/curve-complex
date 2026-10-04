import Mathlib.Geometry.Manifold.Instances.Sphere

open scoped Manifold ContDiff
open Set

@[instance_reducible]
noncomputable def transportedCharts {H X Y : Type*} [TopologicalSpace H]
    [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace H Y]
    (h : X ≃ₜ Y) : ChartedSpace H X where
  atlas := (fun e : OpenPartialHomeomorph Y H => h.transOpenPartialHomeomorph e) '' atlas H Y
  chartAt x := h.transOpenPartialHomeomorph (chartAt H (h x))
  mem_chart_source x := by simpa using mem_chart_source H (h x)
  chart_mem_atlas x := ⟨chartAt H (h x), chart_mem_atlas H (h x), rfl⟩

theorem transportedCharts_transition {H X Y : Type*} [TopologicalSpace H] [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) (e f : OpenPartialHomeomorph Y H) :
    (h.transOpenPartialHomeomorph e).symm.trans (h.transOpenPartialHomeomorph f) =
      e.symm.trans f := by
  ext x <;> simp [Homeomorph.transOpenPartialHomeomorph_eq_trans,
    OpenPartialHomeomorph.trans_source]

theorem transportedCharts_isManifold {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    {H X Y : Type*} [TopologicalSpace H] [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace H Y] (I : ModelWithCorners 𝕜 V H) (n : ℕ∞ω)
    [IsManifold I n Y] (h : X ≃ₜ Y) :
    letI := transportedCharts (H := H) h; IsManifold I n X := by
  letI := transportedCharts (H := H) h
  refine { compatible := ?_ }
  rintro e f ⟨e', he', rfl⟩ ⟨f', hf', rfl⟩
  rw [transportedCharts_transition]
  exact (contDiffGroupoid n I).compatible he' hf'
