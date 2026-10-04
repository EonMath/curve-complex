import CurveComplexGenusTwo.Octagon.SurfaceAssembly.SurfaceAssembly
import Mathlib.LinearAlgebra.Dimension.Finrank

noncomputable section
open CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz
namespace CurveComplex.Octagon

/-- Data certificate for the actual four-edge boundary graph, not a Prop record. -/
structure BoundaryGraphNumericalCertificate where
  h1Iso : H AttachingMap.BoundaryGraph 1 ≅ ModuleCat.of ℤ (Fin 4 → ℤ)
  higherZero : ∀ n : ℕ, 2 ≤ n → IsZero (H AttachingMap.BoundaryGraph n)

/-- Retains the original surface consumer and its concrete graph isomorphism. -/
def actualSurfaceH1Iso (c : BoundaryGraphNumericalCertificate) :
    H Surface 1 ≅ ModuleCat.of ℤ (Fin 4 → ℤ) :=
  boundarySurface_H1_iso.symm ≪≫ c.h1Iso

theorem actualSurfaceH2_kernel (c : BoundaryGraphNumericalCertificate) :
    LinearMap.ker surfaceH2Boundary.hom =
      LinearMap.range ((surfaceHF 2).map (TopCat.ofHom boundaryToSurface)).hom := by
  exact surfaceH2Boundary_graph_kernel

/-- Dimension transport uses the actual iso's linear equivalence. -/
theorem actualSurfaceH1_finrank (c : BoundaryGraphNumericalCertificate) :
    Module.finrank ℤ (H Surface 1) = 4 := by
  rw [(actualSurfaceH1Iso c).toLinearEquiv.finrank_eq]
  simp

/-- Graph H₂ zero eliminates the kernel of the already-surjective actual map. -/
theorem actualSurfaceH2Boundary_isIso (c : BoundaryGraphNumericalCertificate) :
    IsIso surfaceH2Boundary := by
  letI := ModuleCat.subsingleton_of_isZero (c.higherZero 2 (by omega))
  have hmap : ((surfaceHF 2).map (TopCat.ofHom boundaryToSurface)).hom = 0 := by
    apply LinearMap.ext
    intro x
    rw [Subsingleton.elim x 0, map_zero]
    rfl
  haveI : Mono surfaceH2Boundary := by
    apply (ModuleCat.mono_iff_injective _).mpr
    apply LinearMap.ker_eq_bot.mp
    rw [actualSurfaceH2_kernel c, hmap, LinearMap.range_zero]
  letI := surfaceH2Boundary_epi
  exact isIso_of_mono_of_epi _

/-- This iso uses the actual connecting map; it does not select an arbitrary iso. -/
def actualSurfaceH2Iso (c : BoundaryGraphNumericalCertificate) :
    H Surface 2 ≅ ModuleCat.of ℤ ℤ :=
  @asIso _ _ _ _ surfaceH2Boundary (actualSurfaceH2Boundary_isIso c)

end CurveComplex.Octagon
