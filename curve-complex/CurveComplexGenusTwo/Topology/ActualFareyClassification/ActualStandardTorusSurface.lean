import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualOriginalNormalizedEssentialTerminal
import Mathlib.Geometry.Manifold.Instances.Sphere

open Set Topology Schoenflies CurveComplex
open scoped Manifold ContDiff

private abbrev TorusProductModel :=
  ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))
@[reducible] private noncomputable instance : NormedAddCommGroup TorusProductModel :=
  inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)))
@[reducible] private noncomputable instance : NormedSpace ℝ TorusProductModel :=
  inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)))

/-- Construct the standard torus's actual plane-model smooth closed surface
structure from its two actual circle manifolds; no surface instance is assumed. -/
theorem actual_standard_torus_has_closed_surface_structure :
    ∃ C : ChartedSpace Plane (Circle×Circle), @ClosedSurface (Circle×Circle) _ C := by
  let Z := TorusProductModel
  let V := EuclideanSpace ℝ (Fin 1)×EuclideanSpace ℝ (Fin 1)
  let L : V ≃L[ℝ] Plane := (EuclideanSpace.finAddEquivProd (𝕜:=ℝ) (n:=1) (m:=1)).symm
  let Lh : Z ≃ₜ Plane := L.toHomeomorph
  let l := Lh.toOpenPartialHomeomorph
  let C : ChartedSpace Plane (Circle×Circle) := {
    atlas := (fun e : OpenPartialHomeomorph (Circle×Circle) Z => e.trans l) '' atlas Z (Circle×Circle)
    chartAt := fun x => (chartAt Z x).trans l
    mem_chart_source := by intro x; exact ⟨mem_chart_source Z x,mem_univ _⟩
    chart_mem_atlas := by intro x; exact ⟨chartAt Z x,chart_mem_atlas Z x,rfl⟩ }
  have hOld (e e' : OpenPartialHomeomorph (Circle×Circle) Z)
      (he : e∈atlas Z (Circle×Circle)) (he' : e'∈atlas Z (Circle×Circle)) :
      ContDiffOn ℝ ∞ (show V → V from fun z => (e.symm.trans e') z)
        {z : V | z∈(e.symm.trans e').source} := by
    have hh := (contDiffGroupoid ∞ ((𝓡 1).prod (𝓡 1))).compatible he he'
    have hh₁ := hh.1
    simp only [contDiffPregroupoid,mfld_simps,Prod.map,Function.comp_def] at hh₁
    dsimp only [V,Z,TorusProductModel,ModelProd] at *
    convert hh₁ using 1 <;> ext z <;> simp
  let := C
  have hSmooth : IsManifold (𝓡 2) ∞ (Circle×Circle) := by
    apply isManifold_of_contDiffOn (𝓡 2) ∞ (Circle×Circle)
    rintro f f' ⟨e,he,rfl⟩ ⟨e',he',rfl⟩
    have hDomain : ((e.trans l).symm.trans (e'.trans l)).source=
        L.symm ⁻¹' (e.symm.trans e').source := by
      ext z
      simp only [OpenPartialHomeomorph.trans_source,OpenPartialHomeomorph.symm_source,
        OpenPartialHomeomorph.trans_target,mem_inter_iff,mem_preimage]
      simp [l,Lh,OpenPartialHomeomorph.coe_trans_symm]
    have hComp : ContDiffOn ℝ ∞ (fun z : Plane => L ((e.symm.trans e') (L.symm z)))
        (L.symm ⁻¹' (e.symm.trans e').source) :=
      L.contDiff.contDiffOn.comp
        ((hOld e e' he he').comp L.symm.contDiff.contDiffOn (mapsTo_preimage _ _)) (mapsTo_univ _ _)
    convert hComp using 1 <;>
      simp [mfld_simps,l,Lh,OpenPartialHomeomorph.coe_trans_symm,
        OpenPartialHomeomorph.trans_apply,Function.comp_def]; rfl
  let := hSmooth
  refine ⟨C,?_⟩
  exact {
    toT2Space := inferInstance
    toCompactSpace := inferInstance
    toConnectedSpace := inferInstance
    toIsManifold := hSmooth }


#print axioms actual_standard_torus_has_closed_surface_structure
