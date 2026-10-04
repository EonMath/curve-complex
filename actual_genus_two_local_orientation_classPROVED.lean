import ClosedHyperbolicCanonicalBridge
import CurveComplexGenusTwo.Topology.PositionExtension.SurfacePuncture
open CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz
namespace CurveComplex.Hyperbolic
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
theorem actual_genus_two_local_orientation_class (M : HyperellipticModel E S) :
    (∀ x : E, Mono (homologyToRelative E ({x}ᶜ : Set E) 2)) ∧
    ∃ z : integralHomology E 2, z ≠ 0 ∧
      ∀ x : E, homologyToRelative E ({x}ᶜ : Set E) 2 z ≠ 0 := by
  classical
  letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
  have hmono (x : E) : Mono (homologyToRelative E ({x}ᶜ : Set E) 2) := by
    obtain ⟨hz,hexact⟩ := pairHomology_exact_at_absolute E ({x}ᶜ : Set E) 2
    apply hexact.mono_g
    exact CurveComplex.GenusOrientationCandidate.surface_puncture_homologyInclusion_zero x
  obtain ⟨e⟩ := M.genusTwo.2.2.1
  let z : integralHomology E 2 := e.inv (1 : ℤ)
  have hz : z ≠ 0 := by
    intro hz
    have hi := e.inv_hom_id_apply (1 : ℤ)
    change e.hom z = 1 at hi
    rw [hz] at hi
    simpa using hi
  refine ⟨hmono,z,hz,?_⟩
  intro x hx
  letI := hmono x
  apply hz
  apply (ModuleCat.mono_iff_injective (homologyToRelative E ({x}ᶜ : Set E) 2)).mp inferInstance
  change (homologyToRelative E ({x}ᶜ : Set E) 2).hom z =
    (homologyToRelative E ({x}ᶜ : Set E) 2).hom 0
  rw [map_zero]
  exact hx
end CurveComplex.Hyperbolic
