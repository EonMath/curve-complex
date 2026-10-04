import ClosedHyperbolicCanonicalBridge
import CurveComplexGenusTwo.Topology.PositionExtension.SurfacePuncture
open CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz
set_option backward.isDefEq.respectTransparency false
namespace CurveComplex.Hyperbolic
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
theorem actual_global_orientation_from_one_germ (M : HyperellipticModel E S) (f : E ≃ₜ E) (x : E)
    (hpres : ∀ y ∈ ({x}ᶜ : Set E), f y ∈ ({x}ᶜ : Set E))
    (hlocal : pairRelativeHomologyMap ({x}ᶜ : Set E) ({x}ᶜ : Set E)
      ⟨f,f.continuous⟩ hpres 2 = 𝟙 (relativeHomology E ({x}ᶜ : Set E) 2)) :
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom (⟨f,f.continuous⟩ : C(E,E)))) =
        𝟙 (integralHomology E 2) := by
  letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
  have hmono : Mono (homologyToRelative E ({x}ᶜ : Set E) 2) := by
    obtain ⟨hz,hexact⟩ := pairHomology_exact_at_absolute E ({x}ᶜ : Set E) 2
    apply hexact.mono_g
    exact CurveComplex.GenusOrientationCandidate.surface_puncture_homologyInclusion_zero x
  letI := hmono
  have hn := pairRelativeHomologyMap_commutes
    ({x}ᶜ : Set E) ({x}ᶜ : Set E) (⟨f,f.continuous⟩ : C(E,E)) hpres 2
  rw [hlocal,Category.comp_id] at hn
  apply (cancel_mono (homologyToRelative E ({x}ᶜ : Set E) 2)).1
  exact hn.symm.trans (Category.id_comp (homologyToRelative E ({x}ᶜ : Set E) 2)).symm
end CurveComplex.Hyperbolic
