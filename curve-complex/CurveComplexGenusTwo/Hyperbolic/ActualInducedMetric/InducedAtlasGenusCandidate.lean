import CurveComplexGenusTwo.Dictionary.Genus

namespace CurveComplex
open scoped Manifold ContDiff

theorem isGenus_of_induced_smooth_atlas {E : Type} [TopologicalSpace E]
    (oldAtlas newAtlas : ChartedSpace (EuclideanSpace ℝ (Fin 2)) E) (g : ℕ)
    (hgenus : @IsGenus E _ oldAtlas g)
    (hsmooth : letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) E := newAtlas; IsManifold (𝓡 2) ∞ E) :
    @IsGenus E _ newAtlas g := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) E := oldAtlas
  letI : ClosedSurface E := Classical.choice hgenus.2.1
  have ht : T2Space E := inferInstance
  have hc : CompactSpace E := inferInstance
  have hn : ConnectedSpace E := inferInstance
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) E := newAtlas
  letI : T2Space E := ht
  letI : CompactSpace E := hc
  letI : ConnectedSpace E := hn
  letI : IsManifold (𝓡 2) ∞ E := hsmooth
  exact ⟨hgenus.1, ⟨{}⟩, hgenus.2.2⟩

end CurveComplex
