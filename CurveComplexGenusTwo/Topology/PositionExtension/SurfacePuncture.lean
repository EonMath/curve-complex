import CurveComplexGenusTwo.Topology.PositionExtension.LocalOrientationAlgebra
import CurveComplexGenusTwo.Topology.Orientation.SurfaceLocalization
import CurveComplexGenusTwo.Topology.Orientation.SurfaceTopHomologyDetection

open CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz
namespace CurveComplex.GenusOrientationCandidate

/-- A top-dimensional cycle on a connected closed surface which avoids one point
has zero image in the surface's absolute singular homology. -/
theorem surface_puncture_homologyInclusion_zero
    {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (x : S) : homologyInclusion S ({x}ᶜ : Set S) 2 = 0 := by
  classical
  have hdetect (z : integralHomology S 2)
      (hz : ∀ y : S, homologyToRelative S ({y}ᶜ : Set S) 2 z = 0) : z = 0 := by
    exact surface_top_homology_detection S z hz
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro w
  let z : integralHomology S 2 := homologyInclusion S ({x}ᶜ : Set S) 2 w
  have hx : homologyToRelative S ({x}ᶜ : Set S) 2 z = 0 := by
    obtain ⟨heq, _⟩ := pairHomology_exact_at_absolute S ({x}ᶜ : Set S) 2
    have hw := congrArg (fun q => q w) heq
    exact hw
  have hclopen : IsClopen {y : S | homologyToRelative S ({y}ᶜ : Set S) 2 z = 0} :=
    ⟨surface_localization_zero_locus_closed S 2 z,
      homology_localization_zero_locus_open S 2 z⟩
  have huniv := hclopen.eq_univ ⟨x, hx⟩
  have hz : ∀ y : S, homologyToRelative S ({y}ᶜ : Set S) 2 z = 0 := by
    intro y
    have hy : y ∈ {y : S | homologyToRelative S ({y}ᶜ : Set S) 2 z = 0} := by
      rw [huniv]
      exact Set.mem_univ y
    exact hy
  exact hdetect z hz

end CurveComplex.GenusOrientationCandidate
