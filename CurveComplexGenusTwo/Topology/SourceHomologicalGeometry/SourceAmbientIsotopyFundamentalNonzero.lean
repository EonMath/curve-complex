import CurveComplexGenusTwo.Topology.SourceHomologicalGeometry.SourceSameImageFundamentalNonzero

namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex CategoryTheory CategoryTheory.Limits CurveComplexGenusTwo.CWHurewicz
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem curve_fundamental_nonzero_of_ambient_isotopy
    {S : Type} [TopologicalSpace S] (c d : Curve S)
    (himage : AmbientIsotopy.Rel c.image d.image)
    (hc : HomologicalComplex.homologyMap
      (actualSingularFunctor.map (TopCat.ofHom ⟨c.map,c.embedded.continuous⟩)) 1
      CircleFundamentalCycle.fundamentalClass ≠ 0) :
    HomologicalComplex.homologyMap
      (actualSingularFunctor.map (TopCat.ofHom ⟨d.map,d.embedded.continuous⟩)) 1
      CircleFundamentalCycle.fundamentalClass ≠ 0 := by
  classical
  obtain ⟨H,hH⟩ := himage
  obtain ⟨e,he⟩ := H.homeomorphism_at ⟨1,by norm_num⟩
  let ec : Curve S := ⟨e ∘ c.map,e.isEmbedding.comp c.embedded⟩
  have hsame : ec.image = d.image := by
    rw [←hH]
    ext x
    constructor
    · rintro ⟨t,rfl⟩
      exact ⟨c.map t,⟨t,rfl⟩,(he _).symm⟩
    · rintro ⟨y,⟨t,rfl⟩,rfl⟩
      exact ⟨t,he _⟩
  apply curve_fundamental_nonzero_of_same_image ec d hsame
  let ef : C(S,S) := ⟨e,e.continuous⟩
  let K : ContinuousMap.Homotopy (ContinuousMap.id S) ef :=
    { toContinuousMap := H.map
      map_zero_left := H.at_zero
      map_one_left := fun x => (he x).symm }
  have hhom := (show TopCat.Homotopy (𝟙 (TopCat.of S)) (TopCat.ofHom ef) from K).congr_homologyMap_singularChainComplexFunctor (ModuleCat.of ℤ ℤ) 1
  have hfactor : TopCat.ofHom (⟨ec.map,ec.embedded.continuous⟩ : C(Circle,S)) =
      TopCat.ofHom (⟨c.map,c.embedded.continuous⟩ : C(Circle,S)) ≫ TopCat.ofHom ef := by
    rfl
  change HomologicalComplex.homologyMap
      (actualSingularFunctor.map (TopCat.ofHom (⟨ec.map,ec.embedded.continuous⟩ : C(Circle,S)))) 1
      CircleFundamentalCycle.fundamentalClass ≠ 0
  rw [hfactor,actualSingularFunctor.map_comp,HomologicalComplex.homologyMap_comp,←hhom]
  simpa using hc

end CurveComplexGenusTwo.SourceTopology
