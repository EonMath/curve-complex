import CurveComplexGenusTwo.Octagon.SurfaceAssembly.SurfaceActualMV
import CurveComplexGenusTwo.Octagon.SurfaceAssembly.OuterBandRetraction
import CurveComplexGenusTwo.Octagon.AttachingHomologyZero

namespace CurveComplex.Octagon
open CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz

theorem surfaceOverlap_band_H1_zero :
    (surfaceHF 1).map (TopCat.ofHom overlapToBand) = 0 := by
  haveI : IsIso ((surfaceHF 1).map (TopCat.ofHom bandRetraction)) :=
    (bandBoundaryHomologyIso 1).isIso_hom
  apply (cancel_mono ((surfaceHF 1).map (TopCat.ofHom bandRetraction))).mp
  rw [zero_comp, ← Functor.map_comp]
  have he : TopCat.ofHom overlapToBand ≫ TopCat.ofHom bandRetraction =
      TopCat.ofHom overlapUnitDirection ≫ TopCat.ofHom AttachingMap.attachingMap :=
    congrArg TopCat.ofHom overlap_band_retraction_attaching
  rw [he, Functor.map_comp, AttachingMap.attaching_h1_map_zero, comp_zero]

theorem surfaceActualDifference_one_zero : surfaceActualDifference 1 = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change surfaceActualDifference 1 x = (0,0)
  rw [surfaceActualDifference_apply, surfaceOverlap_band_H1_zero,
    surfaceOverlap_face_positive_map_zero 1 (by omega)]
  change (0, -(0 : H bandSet 1)) = (0,0)
  simp

theorem surfaceBand_H1_isIso :
    IsIso ((surfaceHF 1).map (TopCat.ofHom bandToSurface)) := by
  letI := surfaceBand_H1_epi
  haveI : Mono ((surfaceHF 1).map (TopCat.ofHom bandToSurface)) := by
    apply (ModuleCat.mono_iff_injective _).mpr
    apply LinearMap.ker_eq_bot.mp
    rw [surfaceBand_H1_kernel, surfaceOverlap_band_H1_zero]
    exact LinearMap.range_zero
  exact isIso_of_mono_of_epi _

noncomputable def surfaceBand_H1_iso : H bandSet 1 ≅ H Surface 1 := by
  letI := surfaceBand_H1_isIso
  exact asIso ((surfaceHF 1).map (TopCat.ofHom bandToSurface))

theorem surfaceH2Boundary_epi : Epi surfaceH2Boundary := by
  haveI : Epi (surfaceActualConnecting 1) :=
    (surfaceActual_exact_overlap 1).epi_f surfaceActualDifference_one_zero
  dsimp only [surfaceH2Boundary]
  infer_instance

theorem surfaceAttachingH1_zero : surfaceAttachingH1 = 0 := by
  rw [surfaceAttachingH1, surfaceOverlap_band_H1_zero, comp_zero]

noncomputable def boundarySurface_H1_iso :
    H AttachingMap.BoundaryGraph 1 ≅ H Surface 1 :=
  (bandBoundaryHomologyIso 1).symm ≪≫ surfaceBand_H1_iso

def boundaryToSurface : C(AttachingMap.BoundaryGraph, Surface) :=
  ⟨Subtype.val, continuous_subtype_val⟩

theorem surfaceH2Boundary_graph_kernel :
    LinearMap.ker surfaceH2Boundary.hom =
      LinearMap.range ((surfaceHF 2).map (TopCat.ofHom boundaryToSurface)).hom := by
  rw [surfaceH2Boundary_kernel]
  haveI : IsIso ((surfaceHF 2).map (TopCat.ofHom boundaryToBand)) :=
    (bandBoundaryHomologyIso 2).isIso_inv
  have hsurj := (ModuleCat.epi_iff_surjective
    ((surfaceHF 2).map (TopCat.ofHom boundaryToBand))).mp inferInstance
  have he : (surfaceHF 2).map (TopCat.ofHom boundaryToSurface) =
      (surfaceHF 2).map (TopCat.ofHom boundaryToBand) ≫
        (surfaceHF 2).map (TopCat.ofHom bandToSurface) := by
    rw [← Functor.map_comp]
    rfl
  ext x
  constructor
  · rintro ⟨y,hy⟩
    obtain ⟨z,hz⟩ := hsurj y
    refine ⟨z, ?_⟩
    rw [he]
    change (surfaceHF 2).map (TopCat.ofHom bandToSurface)
      ((surfaceHF 2).map (TopCat.ofHom boundaryToBand) z) = x
    rw [hz]
    exact hy
  · rintro ⟨z,hz⟩
    refine ⟨(surfaceHF 2).map (TopCat.ofHom boundaryToBand) z, ?_⟩
    rw [he] at hz
    exact hz

end CurveComplex.Octagon
